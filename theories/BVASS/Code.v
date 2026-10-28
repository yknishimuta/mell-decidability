From Coq Require Import List Vector ZArith Bool Lia Sorting.Permutation
  Classical_Prop.
From Mell.Core Require Import Vector FiniteTree.
From Mell.BVAS Require Import Runs Code.
From Mell.BVASS Require Import Stateful ContextInsertion.

Import ListNotations.

Definition fin_list_permutation_dec {q} (left right : list (Fin.t q)) :
    {Permutation left right} + {~ Permutation left right}.
Proof.
  destruct (fin_forall_dec q
    (fun index => List.count_occ Fin.eq_dec left index =
      List.count_occ Fin.eq_dec right index)
    (fun index => Nat.eq_dec (List.count_occ Fin.eq_dec left index)
      (List.count_occ Fin.eq_dec right index))) as [Hall|Hnot].
  - left. now apply (proj2 (Permutation_count_occ Fin.eq_dec left right)).
  - right. intro Hperm. apply Hnot.
    now apply (proj1 (Permutation_count_occ Fin.eq_dec left right)).
Defined.

Definition sconfig_eq_dec {d q} : forall left right : SConfig d q,
    {left = right} + {left <> right}.
Proof.
  intros [left_state left_counters] [right_state right_counters].
  destruct (Fin.eq_dec left_state right_state) as [->|Hstate].
  - destruct (nvec_eq_dec left_counters right_counters) as [->|Hcounters].
    + left; reflexivity.
    + right. intro Heq. inversion Heq. contradiction.
  - right. intro Heq. inversion Heq. contradiction.
Defined.

Definition srule_eq_dec {d q} : forall left right : SRule d q,
    {left = right} + {left <> right}.
Proof.
  intros [left_inputs left_nonempty left_output left_delta]
    [right_inputs right_nonempty right_output right_delta].
  destruct (List.list_eq_dec Fin.eq_dec left_inputs right_inputs) as [->|Hinputs].
  - destruct (Fin.eq_dec left_output right_output) as [->|Houtput].
    + destruct (zvec_eq_dec left_delta right_delta) as [->|Hdelta].
      * left. f_equal. apply proof_irrelevance.
      * right. intro Heq. inversion Heq. contradiction.
    + right. intro Heq. inversion Heq. contradiction.
  - right. intro Heq. inversion Heq. contradiction.
Defined.

Fixpoint interpret_srun {d q} (S : SBVAS d q) (raw : RawRun) :
    option (SRun d q) :=
  match raw with
  | tree_leaf index =>
      match nth_error (initial_configs S) index with
      | Some config => Some (srun_leaf config)
      | None => None
      end
  | tree_node index children =>
      match nth_error (stateful_rules S) index, interpret_sruns S children with
      | Some rule, Some runs =>
          if fin_list_permutation_dec
              (List.map fst (sruns_configs runs)) (input_states rule)
          then
            match add_displacement (rule_delta rule)
              (List.map snd (sruns_configs runs)) with
            | Some counters =>
                Some (srun_node rule runs (output_state rule, counters))
            | None => None
            end
          else None
      | _, _ => None
      end
  end
with interpret_sruns {d q} (S : SBVAS d q) (raws : RawRuns) :
    option (SRuns d q) :=
  match raws with
  | forest_nil => Some sruns_nil
  | forest_cons raw raws' =>
      match interpret_srun S raw, interpret_sruns S raws' with
      | Some run, Some runs => Some (sruns_cons run runs)
      | _, _ => None
      end
  end.

Lemma interpret_srun_valid : forall d q (S : SBVAS d q),
  (forall raw run, interpret_srun S raw = Some run -> ValidSRun S run) /\
  (forall raws runs, interpret_sruns S raws = Some runs -> ValidSRuns S runs).
Proof.
  intros d q S. apply FiniteTree_FiniteForest_ind.
  - intros index run Hdecode. cbn in Hdecode.
    destruct (nth_error (initial_configs S) index) as [config|] eqn:Hconfig;
      inversion Hdecode; subst.
    constructor. now apply nth_error_In in Hconfig.
  - intros index children IH run Hdecode. cbn in Hdecode.
    destruct (nth_error (stateful_rules S) index) as [rule|] eqn:Hrule;
      [|discriminate].
    destruct (interpret_sruns S children) as [runs|] eqn:Hruns;
      [|discriminate].
    destruct (fin_list_permutation_dec
      (List.map fst (sruns_configs runs)) (input_states rule))
      as [Hstates|Hstates]; [|discriminate].
    destruct (add_displacement (rule_delta rule)
      (List.map snd (sruns_configs runs))) as [counters|] eqn:Happly;
      inversion Hdecode; subst.
    econstructor.
    + now apply nth_error_In in Hrule.
    + eapply IH; eauto.
    + exact Hstates.
    + exact Happly.
    + reflexivity.
  - intros runs Hdecode. cbn in Hdecode. inversion Hdecode; constructor.
  - intros raw IHraw raws IHraws runs Hdecode. cbn in Hdecode.
    destruct (interpret_srun S raw) as [run|] eqn:Hrun; [|discriminate].
    destruct (interpret_sruns S raws) as [tail|] eqn:Htail;
      inversion Hdecode; subst.
    constructor; [eapply IHraw|eapply IHraws]; eauto.
Qed.

Combined Scheme ValidSRun_mutind_code from ValidSRun_ind', ValidSRuns_ind'.

Lemma valid_srun_interpretable_mut : forall d q (S : SBVAS d q),
  (forall run, ValidSRun S run ->
    exists raw, interpret_srun S raw = Some run) /\
  (forall runs, ValidSRuns S runs ->
    exists raws, interpret_sruns S raws = Some runs).
Proof.
  intros d q S. apply ValidSRun_mutind_code.
  - intros config Hin. apply In_nth_error in Hin.
    destruct Hin as [index Hindex]. exists (tree_leaf index). cbn.
    now rewrite Hindex.
  - intros rule children result Hrule Hchildren IHchildren Hstates Happly Houtput.
    apply In_nth_error in Hrule. destruct Hrule as [index Hindex].
    destruct IHchildren as [raws Hraws].
    exists (tree_node index raws). cbn. rewrite Hindex, Hraws.
    destruct (fin_list_permutation_dec
      (List.map fst (sruns_configs children)) (input_states rule))
      as [Hperm|Hperm]; [|contradiction].
    rewrite Happly. destruct result as [state counters]. cbn in Houtput.
    subst state. reflexivity.
  - exists forest_nil. reflexivity.
  - intros run runs Hrun IHrun Hruns IHruns.
    destruct IHrun as [raw Hraw]. destruct IHruns as [raws Hraws].
    exists (forest_cons raw raws). cbn. now rewrite Hraw, Hraws.
Qed.

Definition enumerate_srun {d q} (S : SBVAS d q) (code : nat) :
    option (SRun d q) :=
  match decode_run code with
  | Some raw => interpret_srun S raw
  | None => None
  end.

Lemma enumerate_srun_sound : forall d q (S : SBVAS d q) code run,
    enumerate_srun S code = Some run -> ValidSRun S run.
Proof.
  intros d q S code run Hdecode. unfold enumerate_srun in Hdecode.
  destruct (decode_run code) as [raw|] eqn:Hraw; [|discriminate].
  eapply (proj1 (interpret_srun_valid d q S)); eauto.
Qed.

Lemma enumerate_srun_complete : forall d q (S : SBVAS d q)
    (run : SRun d q), ValidSRun S run ->
    exists code, enumerate_srun S code = Some run.
Proof.
  intros d q S run Hvalid.
  destruct (proj1 (valid_srun_interpretable_mut d q S) run Hvalid)
    as [raw Hraw].
  exists (encode_run raw). unfold enumerate_srun.
  now rewrite decode_run_encode.
Qed.

Definition root_config_leb {d q} (left right : SConfig d q) : bool :=
  if Fin.eq_dec (fst left) (fst right)
  then nvec_leb (snd left) (snd right)
  else false.

Lemma root_config_leb_true_iff : forall d q (left right : SConfig d q),
    root_config_leb left right = true <-> RootConfigLe left right.
Proof.
  intros d q [left_state left_counters] [right_state right_counters].
  unfold root_config_leb, RootConfigLe; cbn.
  destruct (Fin.eq_dec left_state right_state) as [Hstate|Hstate].
  - rewrite nvec_leb_true_iff. tauto.
  - split; [discriminate|intros [Heq _]; contradiction].
Qed.

Definition sconfig_eqb {d q} (left right : SConfig d q) : bool :=
  if sconfig_eq_dec left right then true else false.

Lemma sconfig_eqb_true_iff : forall d q (left right : SConfig d q),
    sconfig_eqb left right = true <-> left = right.
Proof.
  intros. unfold sconfig_eqb.
  destruct (sconfig_eq_dec left right); split; intro H; try discriminate; auto.
Qed.

Definition srule_eqb {d q} (left right : SRule d q) : bool :=
  if srule_eq_dec left right then true else false.

Lemma srule_eqb_true_iff : forall d q (left right : SRule d q),
    srule_eqb left right = true <-> left = right.
Proof.
  intros. unfold srule_eqb.
  destruct (srule_eq_dec left right); split; intro H; try discriminate; auto.
Qed.

Fixpoint ordered_embedb_fuel {d q} (fuel : nat)
    (left right : SRun d q) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match right with
      | srun_leaf right_config =>
          match left with
          | srun_leaf left_config => sconfig_eqb left_config right_config
          | srun_node _ _ _ => false
          end
      | srun_node right_rule right_children right_result =>
          let below := sruns_any_embedb_fuel fuel' left right_children in
          match left with
          | srun_leaf _ => below
          | srun_node left_rule left_children _ =>
              (srule_eqb left_rule right_rule &&
               ordered_embedsb_fuel fuel' left_children right_children) || below
          end
      end
  end
with ordered_embedsb_fuel {d q} (fuel : nat)
    (left right : SRuns d q) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match left, right with
      | sruns_nil, sruns_nil => true
      | sruns_cons left_run left_tail, sruns_cons right_run right_tail =>
          root_config_leb (root_config left_run) (root_config right_run) &&
          ordered_embedb_fuel fuel' left_run right_run &&
          ordered_embedsb_fuel fuel' left_tail right_tail
      | _, _ => false
      end
  end
with sruns_any_embedb_fuel {d q} (fuel : nat) (left : SRun d q)
    (right : SRuns d q) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match right with
      | sruns_nil => false
      | sruns_cons right_run right_tail =>
          ordered_embedb_fuel fuel' left right_run ||
          sruns_any_embedb_fuel fuel' left right_tail
      end
  end.

Lemma ordered_embedb_fuel_correct : forall d q fuel,
  (forall (left right : SRun d q), srun_size right < fuel ->
    ordered_embedb_fuel fuel left right = true <-> OrderedDecorEmbed left right) /\
  (forall (left right : SRuns d q), sruns_size right < fuel ->
    ordered_embedsb_fuel fuel left right = true <-> OrderedDecorEmbeds left right) /\
  (forall (left : SRun d q) (right : SRuns d q), sruns_size right < fuel ->
    sruns_any_embedb_fuel fuel left right = true <->
    exists child, SRunsIn child right /\ OrderedDecorEmbed left child).
Proof.
  intros d q fuel. induction fuel as [|fuel IH].
  - repeat split; intros; lia.
  - destruct IH as [IHrun [IHruns IHany]]. split.
    + intros left right Hsize.
      destruct right as [right_config|right_rule right_children right_result].
      * destruct left as [left_config|left_rule left_children left_result]; cbn.
        -- rewrite sconfig_eqb_true_iff. split.
           ++ intro Heq. subst. constructor.
           ++ intro Hembed. inversion Hembed; reflexivity.
        -- split; [discriminate|intro Hembed; inversion Hembed].
      * cbn in Hsize.
        destruct left as [left_config|left_rule left_children left_result]; cbn.
        -- change (sruns_any_embedb_fuel fuel (srun_leaf left_config)
              right_children = true <->
            OrderedDecorEmbed (srun_leaf left_config)
              (srun_node right_rule right_children right_result)).
           rewrite IHany by lia. split.
           ++ intros [child [Hin Hembed]]. eapply ordered_embed_below; eauto.
           ++ intro Hembed. inversion Hembed; subst.
              eexists. split; eauto.
        -- change
             ((srule_eqb left_rule right_rule &&
               ordered_embedsb_fuel fuel left_children right_children) ||
              sruns_any_embedb_fuel fuel
                (srun_node left_rule left_children left_result)
                right_children = true <->
              OrderedDecorEmbed (srun_node left_rule left_children left_result)
                (srun_node right_rule right_children right_result)).
           rewrite Bool.orb_true_iff. rewrite IHany by lia.
           rewrite Bool.andb_true_iff, srule_eqb_true_iff, IHruns by lia.
           split.
           ++ intros [[Hrule Hchildren]|[child [Hin Hembed]]].
              ** subst right_rule. constructor. exact Hchildren.
              ** eapply ordered_embed_below; eauto.
           ++ intro Hembed. inversion Hembed; subst.
              ** left. auto.
              ** right. eexists. split; eauto.
    + split.
      * intros left right Hsize. destruct right as [|right_run right_tail];
          destruct left as [|left_run left_tail]; cbn in *.
        -- split; [constructor|reflexivity].
        -- split; [discriminate|intro H; inversion H].
        -- split; [discriminate|intro H; inversion H].
        -- rewrite !Bool.andb_true_iff, root_config_leb_true_iff,
            IHrun by lia.
           rewrite IHruns by lia. split.
           ++ intros [[Hroot Hrun] Htail]. constructor; assumption.
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

Definition ordered_embedb {d q} (left right : SRun d q) : bool :=
  ordered_embedb_fuel (S (srun_size right)) left right.

Lemma ordered_embedb_true_iff : forall d q (left right : SRun d q),
    ordered_embedb left right = true <-> OrderedDecorEmbed left right.
Proof.
  intros. apply (proj1 (ordered_embedb_fuel_correct d q _)); lia.
Qed.

Definition strong_srun_leb {d q} (left right : SRun d q) : bool :=
  root_config_leb (root_config left) (root_config right) &&
  ordered_embedb left right.

Lemma strong_srun_leb_true_iff : forall d q (left right : SRun d q),
    strong_srun_leb left right = true <->
    RootConfigLe (root_config left) (root_config right) /\
    OrderedDecorEmbed left right.
Proof.
  intros. unfold strong_srun_leb.
  rewrite Bool.andb_true_iff, root_config_leb_true_iff,
    ordered_embedb_true_iff. tauto.
Qed.

Definition strong_srun_le_dec {d q} (left right : SRun d q) :
    {RootConfigLe (root_config left) (root_config right) /\
      OrderedDecorEmbed left right} +
    {~ (RootConfigLe (root_config left) (root_config right) /\
      OrderedDecorEmbed left right)}.
Proof.
  destruct (strong_srun_leb left right) eqn:Hresult.
  - left. now apply strong_srun_leb_true_iff.
  - right. intro H. apply strong_srun_leb_true_iff in H. congruence.
Defined.
