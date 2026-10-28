From Coq Require Import List Vector VectorSpec Eqdep_dec Arith.PeanoNat
  Arith.Compare_dec Bool Lia ZArith Classical_Prop.
From Mell.Core Require Import Vector FiniteTree Code.
From Mell.BVAS Require Import System Runs Contexts RunOrder.

Import ListNotations.

Definition vector_of_list_exact (d : nat) (values : list nat) : option (NVec d) :=
  match Nat.eq_dec (List.length values) d with
  | left H => Some (eq_rect _ (Vector.t nat) (Vector.of_list values) d H)
  | right _ => None
  end.

Definition encode_nvec {d} (value : NVec d) : nat :=
  list_encode nat_codec (Vector.to_list value).

Definition decode_nvec (d : nat) (code : nat) : option (NVec d) :=
  match list_decode nat_codec code with
  | Some values => vector_of_list_exact d values
  | None => None
  end.

Lemma decode_nvec_encode : forall d (value : NVec d),
    decode_nvec d (encode_nvec value) = Some value.
Proof.
  intros d value. unfold decode_nvec, encode_nvec.
  rewrite list_decode_encode. unfold vector_of_list_exact.
  destruct (Nat.eq_dec (List.length (Vector.to_list value)) d) as [H | H].
  - apply f_equal.
    rewrite (Eqdep_dec.UIP_dec Nat.eq_dec H (length_to_list nat d value)).
    apply of_list_to_list_opp.
  - exfalso. apply H. apply length_to_list.
Qed.

Definition nvec_codec (d : nat) : Codec (NVec d) :=
  {| encode := @encode_nvec d;
     decode := decode_nvec d;
     decode_encode := decode_nvec_encode d |}.

Definition encode_run : RawRun -> nat := tree_encode.
Definition decode_run : nat -> option RawRun := tree_decode.
Definition encode_runs : RawRuns -> nat := forest_encode.
Definition decode_runs : nat -> option RawRuns := forest_decode.

Lemma decode_run_encode : forall run,
    decode_run (encode_run run) = Some run.
Proof. apply tree_decode_encode. Qed.

Lemma decode_runs_encode : forall runs,
    decode_runs (encode_runs runs) = Some runs.
Proof. apply forest_decode_encode. Qed.

Definition run_codec : Codec RawRun := tree_codec.
Definition runs_codec : Codec RawRuns := forest_codec.

Definition zvec_eq_dec {d} : forall left right : ZVec d,
    {left = right} + {left <> right}.
Proof.
  apply Vector.eq_dec with (A_beq := Z.eqb).
  apply Z.eqb_eq.
Defined.

Definition action_eq_dec {d} : forall left right : Action d,
    {left = right} + {left <> right}.
Proof.
  intros [left_arity left_positive left_offset]
    [right_arity right_positive right_offset].
  destruct (Nat.eq_dec left_arity right_arity) as [->|Harity].
  - destruct (zvec_eq_dec left_offset right_offset) as [->|Hoffset].
    + left. f_equal. apply proof_irrelevance.
    + right. intro Heq. inversion Heq. contradiction.
  - right. intro Heq. inversion Heq. contradiction.
Defined.

Definition fin_forall_dec (n : nat) (P : Fin.t n -> Prop)
    (P_dec : forall index, {P index} + {~ P index}) :
    {forall index, P index} + {~ forall index, P index}.
Proof.
  induction n as [|n IH].
  - left. intro index. inversion index.
  - destruct (P_dec Fin.F1) as [Hhead|Hhead].
    + destruct (IH (fun index => P (Fin.FS index))
        (fun index => P_dec (Fin.FS index))) as [Htail|Htail].
      * left. intro index.
        exact (Fin.caseS' index (fun position => P position) Hhead Htail).
      * right. intro Hall. apply Htail. intro index. apply Hall.
    + right. intro Hall. apply Hhead. apply Hall.
Defined.

Definition nvec_le_dec {d} (left right : NVec d) :
    {nvec_le left right} + {~ nvec_le left right} :=
  fin_forall_dec d
    (fun index => Vector.nth left index <= Vector.nth right index)
    (fun index => le_dec (Vector.nth left index) (Vector.nth right index)).

Definition nvec_leb {d} (left right : NVec d) : bool :=
  if nvec_le_dec left right then true else false.

Lemma nvec_leb_true_iff : forall d (left right : NVec d),
    nvec_leb left right = true <-> nvec_le left right.
Proof.
  intros d left right. unfold nvec_leb.
  destruct (nvec_le_dec left right); split; intro H; try discriminate; auto.
Qed.

Definition nvec_eqb {d} (left right : NVec d) : bool :=
  if nvec_eq_dec left right then true else false.

Lemma nvec_eqb_true_iff : forall d (left right : NVec d),
    nvec_eqb left right = true <-> left = right.
Proof.
  intros d left right. unfold nvec_eqb.
  destruct (nvec_eq_dec left right); split; intro H; try discriminate; auto.
Qed.

Definition action_eqb {d} (left right : Action d) : bool :=
  if action_eq_dec left right then true else false.

Lemma action_eqb_true_iff : forall d (left right : Action d),
    action_eqb left right = true <-> left = right.
Proof.
  intros d left right. unfold action_eqb.
  destruct (action_eq_dec left right); split; intro H; try discriminate; auto.
Qed.

Fixpoint irun_size {d} (run : IRun d) : nat :=
  match run with
  | irun_leaf _ => 1
  | irun_node _ children _ => S (iruns_size children)
  end
with iruns_size {d} (runs : IRuns d) : nat :=
  match runs with
  | iruns_nil => 0
  | iruns_cons run tail => S (irun_size run + iruns_size tail)
  end.

Fixpoint irun_embedb_fuel {d} (fuel : nat) (left right : IRun d) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match right with
      | irun_leaf right_value =>
          match left with
          | irun_leaf left_value => nvec_eqb left_value right_value
          | irun_node _ _ _ => false
          end
      | irun_node right_action right_children right_target =>
          let below := iruns_any_embedb_fuel fuel' left right_children in
          match left with
          | irun_leaf _ => below
          | irun_node left_action left_children left_target =>
              (action_eqb left_action right_action &&
               nvec_leb left_target right_target &&
               iruns_embedb_fuel fuel' left_children right_children) || below
          end
      end
  end
with iruns_embedb_fuel {d} (fuel : nat) (left right : IRuns d) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match left, right with
      | iruns_nil, iruns_nil => true
      | iruns_cons left_run left_tail, iruns_cons right_run right_tail =>
          nvec_leb (irun_target left_run) (irun_target right_run) &&
          irun_embedb_fuel fuel' left_run right_run &&
          iruns_embedb_fuel fuel' left_tail right_tail
      | _, _ => false
      end
  end
with iruns_any_embedb_fuel {d} (fuel : nat) (left : IRun d)
    (right : IRuns d) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match right with
      | iruns_nil => false
      | iruns_cons right_run right_tail =>
          irun_embedb_fuel fuel' left right_run ||
          iruns_any_embedb_fuel fuel' left right_tail
      end
  end.

Lemma irun_embedb_fuel_correct : forall d fuel,
  (forall (left right : IRun d), irun_size right < fuel ->
    irun_embedb_fuel fuel left right = true <-> IRunEmbed left right) /\
  (forall (left right : IRuns d), iruns_size right < fuel ->
    iruns_embedb_fuel fuel left right = true <-> IRunsEmbed left right) /\
  (forall (left : IRun d) (right : IRuns d), iruns_size right < fuel ->
    iruns_any_embedb_fuel fuel left right = true <->
    exists child, IRunsIn child right /\ IRunEmbed left child).
Proof.
  intros d fuel. induction fuel as [|fuel IH].
  - repeat split; intros; lia.
  - destruct IH as [IHrun [IHruns IHany]]. split.
    + intros left right Hsize. destruct right as [right_value|right_action right_children right_target].
      * destruct left as [left_value|left_action left_children left_target]; cbn.
        -- rewrite nvec_eqb_true_iff. split.
           ++ intro Heq. subst. constructor.
           ++ intro Hembed. inversion Hembed; reflexivity.
        -- split; [discriminate|intro Hembed; inversion Hembed].
      * cbn in Hsize.
        destruct left as [left_value|left_action left_children left_target]; cbn.
        -- change (iruns_any_embedb_fuel fuel (irun_leaf left_value)
              right_children = true <->
            IRunEmbed (irun_leaf left_value)
              (irun_node right_action right_children right_target)).
           rewrite IHany by lia. split.
           ++ intros [child [Hin Hembed]]. eapply embed_below; eauto.
           ++ intro Hembed. inversion Hembed; subst.
              eexists. split; eauto.
        -- change
             ((action_eqb left_action right_action &&
               nvec_leb left_target right_target &&
               iruns_embedb_fuel fuel left_children right_children) ||
              iruns_any_embedb_fuel fuel
                (irun_node left_action left_children left_target)
                right_children = true <->
              IRunEmbed (irun_node left_action left_children left_target)
                (irun_node right_action right_children right_target)).
           rewrite Bool.orb_true_iff.
           rewrite IHany by lia.
           rewrite !Bool.andb_true_iff,
             action_eqb_true_iff, nvec_leb_true_iff, IHruns by lia.
           split.
           ++ intros [[[Haction Htarget] Hchildren]|[child [Hin Hembed]]].
              ** subst right_action. constructor; assumption.
              ** eapply embed_below; eauto.
           ++ intro Hembed. inversion Hembed; subst.
              ** left. repeat split; assumption.
              ** right. eexists. split; eauto.
    + split.
      * intros left right Hsize. destruct right as [|right_run right_tail];
        destruct left as [|left_run left_tail]; cbn in *.
        -- split; [constructor|reflexivity].
        -- split; [discriminate|intro H; inversion H].
        -- split; [discriminate|intro H; inversion H].
        -- rewrite !Bool.andb_true_iff, nvec_leb_true_iff,
            IHrun by lia.
           rewrite IHruns by lia.
           split.
           ++ intros [[Htarget Hrun] Htail]. constructor; assumption.
           ++ intro Hembed. inversion Hembed; subst. auto.
      * intros left right Hsize. destruct right as [|right_run right_tail]; cbn in *.
        -- split; [discriminate|intros [child [Hin _]]; inversion Hin].
        -- rewrite Bool.orb_true_iff, IHrun by lia.
           rewrite IHany by lia. split.
           ++ intros [Hhead|[child [Hin Hembed]]].
              ** exists right_run. split; [constructor|assumption].
              ** exists child. split; [constructor 2; assumption|assumption].
           ++ intros [child [Hin Hembed]]. inversion Hin; subst.
              ** now left.
              ** right. eexists. split; eauto.
Qed.

Definition irun_embedb {d} (left right : IRun d) : bool :=
  irun_embedb_fuel (S (irun_size right)) left right.

Lemma irun_embedb_true_iff : forall d (left right : IRun d),
    irun_embedb left right = true <-> IRunEmbed left right.
Proof.
  intros. apply (proj1 (irun_embedb_fuel_correct d _)); lia.
Qed.

Definition irun_leb {d} (left right : IRun d) : bool :=
  nvec_leb (irun_target left) (irun_target right) && irun_embedb left right.

Lemma irun_leb_true_iff : forall d (left right : IRun d),
    irun_leb left right = true <-> IRunLe left right.
Proof.
  intros. unfold irun_leb, IRunLe.
  rewrite Bool.andb_true_iff, nvec_leb_true_iff, irun_embedb_true_iff.
  tauto.
Qed.

Definition irun_le_dec {d} (left right : IRun d) :
    {IRunLe left right} + {~ IRunLe left right}.
Proof.
  destruct (irun_leb left right) eqn:Hresult.
  - left. now apply irun_leb_true_iff.
  - right. intro H. apply irun_leb_true_iff in H. congruence.
Defined.

Combined Scheme ValidIRun_mutind_code from ValidIRun_ind', ValidIRuns_ind'.

Lemma valid_irun_interpretable_mut : forall d (S : IBVAS d),
  (forall run, ValidIRun S run ->
    exists raw, interpret_run S raw = Some run) /\
  (forall runs, ValidIRuns S runs ->
    exists raws, interpret_runs S raws = Some runs).
Proof.
  intros d S. apply ValidIRun_mutind_code.
  - intros value Hin. apply In_nth_error in Hin.
    destruct Hin as [index Hindex]. exists (tree_leaf index). cbn.
    now rewrite Hindex.
  - intros action children target Haction Hchildren IHchildren Happly.
    apply In_nth_error in Haction. destruct Haction as [index Hindex].
    destruct IHchildren as [raws Hraws]. exists (tree_node index raws). cbn.
    now rewrite Hindex, Hraws, Happly.
  - exists forest_nil. reflexivity.
  - intros run runs Hrun IHrun Hruns IHruns.
    destruct IHrun as [raw Hraw]. destruct IHruns as [raws Hraws].
    exists (forest_cons raw raws). cbn. now rewrite Hraw, Hraws.
Qed.

Definition enumerate_irun {d} (S : IBVAS d) (code : nat) : option (IRun d) :=
  match decode_run code with
  | Some raw => interpret_run S raw
  | None => None
  end.

Lemma enumerate_irun_sound : forall d (S : IBVAS d) code run,
    enumerate_irun S code = Some run -> ValidIRun S run.
Proof.
  intros d S code run Hdecode. unfold enumerate_irun in Hdecode.
  destruct (decode_run code) as [raw|] eqn:Hraw; [|discriminate].
  eapply (proj1 (interpret_run_valid d S)); eauto.
Qed.

Lemma enumerate_irun_complete : forall d (S : IBVAS d)
    (run : IRun d) (Hvalid : ValidIRun S run),
    exists code, enumerate_irun S code = Some run.
Proof.
  intros d S run Hvalid.
  destruct (proj1 (valid_irun_interpretable_mut d S) run Hvalid)
    as [raw Hraw].
  exists (encode_run raw). unfold enumerate_irun.
  now rewrite decode_run_encode.
Qed.
