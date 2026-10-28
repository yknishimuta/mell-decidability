From Coq Require Import Bool Lia List QArith.
From Mell.Geometry Require Import MathCompBridge RationalDefinability
  RationalQEOne.

Import ListNotations.
Open Scope Q_scope.

Definition QAffineDNF := list QAffineConjunction.

Definition qaffine_dnf_semantics (environment : QEnvironment)
    (dnf : QAffineDNF) : Prop :=
  exists cell, List.In cell dnf /\ qconjunction_semantics environment cell.

Definition qaffine_atom_closed (bound : nat) (atom : QAffineAtom) : bool :=
  match atom with
  | QAEq lhs rhs =>
      qterm_closed bound lhs && qterm_closed bound rhs
  | QALe lhs rhs =>
      qterm_closed bound lhs && qterm_closed bound rhs
  | QALt lhs rhs =>
      qterm_closed bound lhs && qterm_closed bound rhs
  end.

Definition qaffine_conjunction_closed (bound : nat)
    (cell : QAffineConjunction) : Prop :=
  List.Forall (fun atom => qaffine_atom_closed bound atom = true) cell.

Definition qaffine_dnf_closed (bound : nat) (dnf : QAffineDNF) : Prop :=
  List.Forall (qaffine_conjunction_closed bound) dnf.

Lemma qaffine_singleton_correct : forall environment atom,
    qaffine_dnf_semantics environment [[atom]] <->
    qaffine_atom_semantics environment atom.
Proof.
  intros environment atom. unfold qaffine_dnf_semantics,
    qconjunction_semantics. split.
  - intros [cell [[<-|[]] Hsem]]. inversion Hsem; subst. exact H1.
  - intro Hsem. exists [atom]. split; [now left|].
    constructor; [exact Hsem|constructor].
Qed.

Lemma qaffine_equality_correct : forall environment left right,
    qaffine_dnf_semantics environment
      [[QALe left right; QALe right left]] <->
    qterm_semantics environment left == qterm_semantics environment right.
Proof.
  intros environment left right. unfold qaffine_dnf_semantics,
    qconjunction_semantics. split.
  - intros [cell [[<-|[]] Hsem]]. inversion Hsem as [|? ? Hle Htail]; subst.
    inversion Htail as [|? ? Hge Hnil]; subst. cbn in Hle, Hge.
    apply Qle_antisym; assumption.
  - intro Heq. exists [QALe left right; QALe right left].
    split; [now left|]. constructor.
    + cbn. setoid_rewrite Heq. apply Qle_refl.
    + constructor; [cbn; setoid_rewrite Heq; apply Qle_refl|constructor].
Qed.

Definition qaffine_dnf_or (left right : QAffineDNF) : QAffineDNF :=
  left ++ right.

Definition qaffine_dnf_and (left right : QAffineDNF) : QAffineDNF :=
  List.flat_map (fun left_cell =>
    List.map (fun right_cell => left_cell ++ right_cell) right) left.

Lemma qaffine_dnf_or_correct : forall environment left right,
    qaffine_dnf_semantics environment (qaffine_dnf_or left right) <->
    qaffine_dnf_semantics environment left \/
    qaffine_dnf_semantics environment right.
Proof.
  intros environment left right. unfold qaffine_dnf_semantics,
    qaffine_dnf_or. split.
  - intros [cell [Hin Hsem]]. apply in_app_or in Hin. destruct Hin.
    + left. exists cell. auto.
    + right. exists cell. auto.
  - intros [[cell [Hin Hsem]]|[cell [Hin Hsem]]].
    + exists cell. split; [apply in_or_app; now left|exact Hsem].
    + exists cell. split; [apply in_or_app; now right|exact Hsem].
Qed.

Lemma qaffine_dnf_and_correct : forall environment left right,
    qaffine_dnf_semantics environment (qaffine_dnf_and left right) <->
    qaffine_dnf_semantics environment left /\
    qaffine_dnf_semantics environment right.
Proof.
  intros environment left right. unfold qaffine_dnf_semantics,
    qaffine_dnf_and. split.
  - intros [cell [Hin Hsem]]. apply in_flat_map in Hin.
    destruct Hin as [left_cell [Hleft Hin]].
    apply in_map_iff in Hin. destruct Hin as [right_cell [<- Hright]].
    apply Forall_app in Hsem as [Hleft_sem Hright_sem]. split.
    + exists left_cell. auto.
    + exists right_cell. auto.
  - intros [[left_cell [Hleft Hleft_sem]]
      [right_cell [Hright Hright_sem]]].
    exists (left_cell ++ right_cell). split.
    + apply in_flat_map. exists left_cell. split; [exact Hleft|].
      apply in_map. exact Hright.
    + apply Forall_app. auto.
Qed.

Definition qaffine_atom_semantics_dec environment atom :
    {qaffine_atom_semantics environment atom} +
    {~ qaffine_atom_semantics environment atom}.
Proof.
  destruct atom as [left right|left right|left right]; cbn.
  - apply Qeq_dec.
  - destruct (Qlt_le_dec (qterm_semantics environment right)
      (qterm_semantics environment left)) as [Hlt|Hle].
    + right. exact (Qlt_not_le _ _ Hlt).
    + left. exact Hle.
  - destruct (Qlt_le_dec (qterm_semantics environment left)
      (qterm_semantics environment right)) as [Hlt|Hle].
    + left. exact Hlt.
    + right. intro Hcontra. exact (Qlt_not_le _ _ Hcontra Hle).
Defined.

Fixpoint qconjunction_semantics_dec environment cell :
    {qconjunction_semantics environment cell} +
    {~ qconjunction_semantics environment cell}.
Proof.
  destruct cell as [|atom tail].
  - left. constructor.
  - destruct (qaffine_atom_semantics_dec environment atom) as [Hatom|Hatom];
      destruct (qconjunction_semantics_dec environment tail) as [Htail|Htail].
    + left. constructor; assumption.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
Defined.

Fixpoint qaffine_dnf_semantics_dec environment dnf :
    {qaffine_dnf_semantics environment dnf} +
    {~ qaffine_dnf_semantics environment dnf}.
Proof.
  destruct dnf as [|cell tail].
  - right. intros [body [[] _]].
  - destruct (qconjunction_semantics_dec environment cell) as [Hcell|Hcell].
    + left. exists cell. split; [now left|exact Hcell].
    + destruct (qaffine_dnf_semantics_dec environment tail) as [Htail|Htail].
      * left. destruct Htail as [body [Hin Hsem]]. exists body.
        split; [now right|exact Hsem].
      * right. intros [body [[<-|Hin] Hsem]].
        -- contradiction.
        -- apply Htail. exists body. auto.
Defined.

Definition qaffine_atom_neg (atom : QAffineAtom) : QAffineDNF :=
  match atom with
  | QAEq lhs rhs => [[QALt lhs rhs]; [QALt rhs lhs]]
  | QALe lhs rhs => [[QALt rhs lhs]]
  | QALt lhs rhs => [[QALe rhs lhs]]
  end.

Lemma qaffine_atom_neg_correct : forall environment atom,
    qaffine_dnf_semantics environment (qaffine_atom_neg atom) <->
    ~ qaffine_atom_semantics environment atom.
Proof.
  intros environment [left right|left right|left right]; cbn;
    unfold qaffine_dnf_semantics, qconjunction_semantics; cbn.
  - split.
    + intros [cell [[<-|[<-|[]]] Hsem]].
      * inversion Hsem as [|? ? Hlt _]; subst; cbn in Hlt.
        exact (Qlt_not_eq _ _ Hlt).
      * inversion Hsem as [|? ? Hlt _]; subst; cbn in Hlt.
        intro Heq. apply (Qlt_not_eq _ _ Hlt). now symmetry.
    + intro Hneq. destruct (Qlt_le_dec (qterm_semantics environment left)
        (qterm_semantics environment right)) as [Hlt|Hle].
      * exists [QALt left right]. cbn. auto.
      * assert (Hrev : qterm_semantics environment right <
            qterm_semantics environment left).
        { destruct (Qle_lt_or_eq _ _ Hle) as [Hlt|Heq]; [exact Hlt|].
          exfalso. apply Hneq. now symmetry. }
        exists [QALt right left]. cbn. auto.
  - split.
    + intros [cell [[<-|[]] Hsem]]. inversion Hsem; subst; cbn in *.
      exact (Qlt_not_le _ _ H1).
    + intro Hnot. exists [QALt right left]. split; [now left|].
      constructor; [apply Qnot_le_lt; exact Hnot|constructor].
  - split.
    + intros [cell [[<-|[]] Hsem]]. inversion Hsem; subst; cbn in *.
      exact (Qle_not_lt _ _ H1).
    + intro Hnot. exists [QALe right left]. split; [now left|].
      constructor; [apply Qnot_lt_le; exact Hnot|constructor].
Qed.

Fixpoint qaffine_conjunction_neg (cell : QAffineConjunction) : QAffineDNF :=
  match cell with
  | [] => []
  | atom :: tail => qaffine_dnf_or (qaffine_atom_neg atom)
      (qaffine_conjunction_neg tail)
  end.

Lemma qaffine_conjunction_neg_correct : forall environment cell,
    qaffine_dnf_semantics environment (qaffine_conjunction_neg cell) <->
    ~ qconjunction_semantics environment cell.
Proof.
  intros environment cell. induction cell as [|atom tail IH]; cbn.
  - unfold qaffine_dnf_semantics. split.
    + intros [body [[] _]].
    + intro H. exfalso. apply H. constructor.
  - rewrite qaffine_dnf_or_correct, qaffine_atom_neg_correct, IH.
    unfold qconjunction_semantics. rewrite Forall_cons_iff.
    destruct (qaffine_atom_semantics_dec environment atom); tauto.
Qed.

Fixpoint qaffine_dnf_neg (dnf : QAffineDNF) : QAffineDNF :=
  match dnf with
  | [] => [[]]
  | cell :: tail => qaffine_dnf_and (qaffine_conjunction_neg cell)
      (qaffine_dnf_neg tail)
  end.

Theorem qaffine_dnf_neg_correct : forall environment dnf,
    qaffine_dnf_semantics environment (qaffine_dnf_neg dnf) <->
    ~ qaffine_dnf_semantics environment dnf.
Proof.
  intros environment dnf. induction dnf as [|cell tail IH]; cbn.
  - unfold qaffine_dnf_semantics, qconjunction_semantics. split.
    + intros [body [[<-|[]] Hsem]] [other [[] _]].
    + intro Hempty. exists []. cbn. auto.
  - rewrite qaffine_dnf_and_correct, qaffine_conjunction_neg_correct, IH.
    change ((~ qconjunction_semantics environment cell) /\
      ~ qaffine_dnf_semantics environment tail <->
      ~ (exists body, List.In body (cell :: tail) /\
          qconjunction_semantics environment body)).
    split.
    + intros [Hcell Htail] [body [[<-|Hin] Hsem]].
      * apply Hcell. exact Hsem.
      * apply Htail. exists body. auto.
    + intro Hnot. split.
      * intro Hcell. apply Hnot. exists cell.
        split; [now left|exact Hcell].
      * intros [body [Hin Hsem]]. apply Hnot. exists body.
        split; [now right|exact Hsem].
Qed.

Definition qoutput_atom_to_affine (atom : QOutputAtom) : QAffineAtom :=
  if output_strict atom
  then QALt (output_left atom) (output_right atom)
  else QALe (output_left atom) (output_right atom).

Definition qoutput_conjunction_to_affine
    (cell : QOutputConjunction) : QAffineConjunction :=
  List.map qoutput_atom_to_affine cell.

Lemma qoutput_conjunction_to_affine_correct : forall environment cell,
    qconjunction_semantics environment
      (qoutput_conjunction_to_affine cell) <->
    qoutput_conjunction_semantics environment cell.
Proof.
  intros environment cell. unfold qconjunction_semantics,
    qoutput_conjunction_semantics, qoutput_conjunction_to_affine.
  induction cell as [|atom tail IH]; cbn.
  - split; intro H; constructor.
  - rewrite !Forall_cons_iff, IH. unfold qoutput_atom_to_affine,
      qaffine_atom_semantics, qoutput_atom_semantics.
    destruct (output_strict atom); reflexivity.
Qed.

Definition qoutput_dnf_to_affine (dnf : QDNF) : QAffineDNF :=
  List.map qoutput_conjunction_to_affine dnf.

Lemma qoutput_dnf_to_affine_correct : forall environment dnf,
    qaffine_dnf_semantics environment (qoutput_dnf_to_affine dnf) <->
    qdnf_semantics environment dnf.
Proof.
  intros environment dnf. unfold qaffine_dnf_semantics,
    qoutput_dnf_to_affine, qdnf_semantics. split.
  - intros [cell [Hin Hsem]]. apply in_map_iff in Hin.
    destruct Hin as [source [<- Hin]]. exists source. split; [exact Hin|].
    apply (proj1 (qoutput_conjunction_to_affine_correct _ _)). exact Hsem.
  - intros [source [Hin Hsem]]. exists (qoutput_conjunction_to_affine source).
    split; [apply in_map; exact Hin|].
    apply (proj2 (qoutput_conjunction_to_affine_correct _ _)). exact Hsem.
Qed.

Definition qaffine_dnf_exists (dnf : QAffineDNF) : QAffineDNF :=
  List.flat_map (fun cell => qoutput_dnf_to_affine (eliminate_one cell)) dnf.

Lemma qaffine_dnf_exists_correct : forall environment dnf,
    qaffine_dnf_semantics environment (qaffine_dnf_exists dnf) <->
    exists bound,
      qaffine_dnf_semantics (qenvironment_extend environment bound) dnf.
Proof.
  intros environment dnf. unfold qaffine_dnf_exists,
    qaffine_dnf_semantics. split.
  - intros [output [Hin Hsem]]. apply in_flat_map in Hin.
    destruct Hin as [cell [Hcell Houtput]].
    assert (Hout : qaffine_dnf_semantics environment
        (qoutput_dnf_to_affine (eliminate_one cell))).
    { exists output. split; assumption. }
    apply qoutput_dnf_to_affine_correct in Hout.
    apply (proj2 (eliminate_one_correct cell environment)) in Hout.
    destruct Hout as [bound Hbody]. exists bound, cell. split; assumption.
  - intros [bound [cell [Hcell Hsem]]].
    assert (Hout : qdnf_semantics environment (eliminate_one cell)).
    { apply (proj1 (eliminate_one_correct cell environment)). exists bound.
      exact Hsem. }
    apply (proj2 (qoutput_dnf_to_affine_correct environment
      (eliminate_one cell))) in Hout.
    destruct Hout as [output [Houtput Houtput_sem]].
    exists output. split; [|exact Houtput_sem].
    apply in_flat_map. exists cell. split; assumption.
Qed.

Fixpoint qformula_to_dnf (formula : QFormula) : QAffineDNF :=
  match formula with
  | QFTop => [[]]
  | QFBot => []
  | QFEq lhs rhs => [[QALe lhs rhs; QALe rhs lhs]]
  | QFLt lhs rhs => [[QALt lhs rhs]]
  | QFLe lhs rhs => [[QALe lhs rhs]]
  | QFAnd lhs rhs =>
      qaffine_dnf_and (qformula_to_dnf lhs) (qformula_to_dnf rhs)
  | QFOr lhs rhs =>
      qaffine_dnf_or (qformula_to_dnf lhs) (qformula_to_dnf rhs)
  | QFNot body => qaffine_dnf_neg (qformula_to_dnf body)
  | QFExists body => qaffine_dnf_exists (qformula_to_dnf body)
  | QFForall body => qaffine_dnf_neg
      (qaffine_dnf_exists (qaffine_dnf_neg (qformula_to_dnf body)))
  end.

Theorem qformula_to_dnf_correct : forall formula environment,
    qformula_semantics environment formula <->
    qaffine_dnf_semantics environment (qformula_to_dnf formula).
Proof.
  intro formula. induction formula; intro environment; cbn.
  - unfold qaffine_dnf_semantics, qconjunction_semantics. split.
    + intro Htop. exists []. cbn. auto.
    + tauto.
  - unfold qaffine_dnf_semantics. split; [tauto|intros [cell [[] _]]].
  - symmetry. apply qaffine_equality_correct.
  - symmetry. apply qaffine_singleton_correct.
  - symmetry. apply qaffine_singleton_correct.
  - rewrite qaffine_dnf_and_correct, <- IHformula1, <- IHformula2.
    reflexivity.
  - rewrite qaffine_dnf_or_correct, <- IHformula1, <- IHformula2.
    reflexivity.
  - rewrite qaffine_dnf_neg_correct, <- IHformula. reflexivity.
  - rewrite qaffine_dnf_exists_correct. split.
    + intros [bound Hbody]. exists bound. apply (proj1 (IHformula _)). exact Hbody.
    + intros [bound Hbody]. exists bound. apply (proj2 (IHformula _)). exact Hbody.
  - rewrite qaffine_dnf_neg_correct, qaffine_dnf_exists_correct.
    split.
    + intros Hall [bound Hnegative].
      apply qaffine_dnf_neg_correct in Hnegative.
      apply Hnegative. apply (proj1 (IHformula _)). apply Hall.
    + intros Hnot bound. apply (proj2 (IHformula _)).
      destruct (qaffine_dnf_semantics_dec
        (qenvironment_extend environment bound) (qformula_to_dnf formula))
        as [Hbody|Hbody]; [exact Hbody|].
      exfalso. apply Hnot. exists bound.
      apply (proj2 (qaffine_dnf_neg_correct _ _)). exact Hbody.
Qed.

Lemma qaffine_dnf_or_closed : forall bound left right,
    qaffine_dnf_closed bound left -> qaffine_dnf_closed bound right ->
    qaffine_dnf_closed bound (qaffine_dnf_or left right).
Proof. intros. unfold qaffine_dnf_closed, qaffine_dnf_or. now apply Forall_app. Qed.

Lemma qaffine_dnf_and_closed : forall bound left right,
    qaffine_dnf_closed bound left -> qaffine_dnf_closed bound right ->
    qaffine_dnf_closed bound (qaffine_dnf_and left right).
Proof.
  intros bound left right Hleft Hright. unfold qaffine_dnf_closed,
    qaffine_dnf_and in *. rewrite Forall_flat_map. apply Forall_forall.
  intros left_cell Hleft_in. apply Forall_forall with (x := left_cell)
    in Hleft; [|exact Hleft_in]. rewrite Forall_map. apply Forall_forall.
  intros right_cell Hright_in. apply Forall_forall with (x := right_cell)
    in Hright; [|exact Hright_in].
  unfold qaffine_conjunction_closed in *. apply Forall_app. auto.
Qed.

Lemma qaffine_atom_neg_closed : forall bound atom,
    qaffine_atom_closed bound atom = true ->
    qaffine_dnf_closed bound (qaffine_atom_neg atom).
Proof.
  intros bound [left right|left right|left right] Hclosed; cbn in *;
    apply andb_true_iff in Hclosed as [Hleft Hright];
    unfold qaffine_dnf_closed, qaffine_conjunction_closed; cbn;
    repeat constructor; cbn; rewrite ?Hleft, ?Hright; reflexivity.
Qed.

Lemma qaffine_conjunction_neg_closed : forall bound cell,
    qaffine_conjunction_closed bound cell ->
    qaffine_dnf_closed bound (qaffine_conjunction_neg cell).
Proof.
  intros bound cell Hclosed. induction Hclosed; cbn.
  - unfold qaffine_dnf_closed. constructor.
  - apply qaffine_dnf_or_closed; [apply qaffine_atom_neg_closed|]; assumption.
Qed.

Lemma qaffine_dnf_neg_closed : forall bound dnf,
    qaffine_dnf_closed bound dnf ->
    qaffine_dnf_closed bound (qaffine_dnf_neg dnf).
Proof.
  intros bound dnf Hclosed. induction Hclosed; cbn.
  - unfold qaffine_dnf_closed, qaffine_conjunction_closed. cbn.
    repeat constructor.
  - apply qaffine_dnf_and_closed.
    + apply qaffine_conjunction_neg_closed. exact H.
    + exact IHHclosed.
Qed.

Lemma separate_term_tail_closed : forall term bound,
    qterm_closed (S bound) term = true ->
    qterm_closed bound (separated_tail (separate_term term)) = true.
Proof.
  intro term. induction term; intros bound Hclosed; cbn in *.
  - destruct n as [|n]; cbn in *; [reflexivity|].
    apply Nat.ltb_lt. apply Nat.ltb_lt in Hclosed. lia.
  - reflexivity.
  - apply andb_true_iff in Hclosed as [Hleft Hright].
    apply andb_true_iff. split; [apply IHterm1|apply IHterm2]; assumption.
  - apply IHterm. exact Hclosed.
  - apply IHterm. exact Hclosed.
Qed.

Definition qconstraint_rhs_closed (bound : nat)
    (constraint : QLinearConstraint) : Prop :=
  qterm_closed bound (constraint_rhs constraint) = true.

Lemma normalize_difference_rhs_closed : forall bound left right,
    qterm_closed (S bound) left = true ->
    qterm_closed (S bound) right = true ->
    qconstraint_rhs_closed bound (normalize_difference left right).
Proof.
  intros bound left right Hleft Hright. unfold qconstraint_rhs_closed,
    normalize_difference, qterm_minus. cbn.
  apply andb_true_iff. split.
  - apply separate_term_tail_closed. exact Hright.
  - apply separate_term_tail_closed. exact Hleft.
Qed.

Lemma normalize_atom_rhs_closed : forall bound atom,
    qaffine_atom_closed (S bound) atom = true ->
    List.Forall (qconstraint_rhs_closed bound) (normalize_atom atom).
Proof.
  intros bound [left right|left right|left right] Hclosed; cbn in Hclosed;
    apply andb_true_iff in Hclosed as [Hleft Hright]; cbn.
  - constructor.
    + apply normalize_difference_rhs_closed; assumption.
    + constructor; [apply normalize_difference_rhs_closed; assumption|constructor].
  - constructor; [apply normalize_difference_rhs_closed; assumption|constructor].
  - constructor; [apply normalize_difference_rhs_closed; assumption|constructor].
Qed.

Lemma normalize_conjunction_rhs_closed : forall bound cell,
    qaffine_conjunction_closed (S bound) cell ->
    List.Forall (qconstraint_rhs_closed bound) (normalize_conjunction cell).
Proof.
  intros bound cell Hclosed. induction Hclosed; cbn; [constructor|].
  apply Forall_app. split; [apply normalize_atom_rhs_closed|]; assumption.
Qed.

Definition qendpoint_closed (bound : nat) (endpoint : QEndpoint) : Prop :=
  qterm_closed bound (endpoint_term endpoint) = true.

Definition qelim_state_closed (bound : nat) (state : QElimState) : Prop :=
  List.Forall (qendpoint_closed bound) (state_residual state) /\
  List.Forall (qendpoint_closed bound) (state_lower state) /\
  List.Forall (qendpoint_closed bound) (state_upper state).

Lemma endpoint_of_constraint_closed : forall bound constraint,
    qconstraint_rhs_closed bound constraint ->
    qendpoint_closed bound (endpoint_of_constraint constraint).
Proof. intros. unfold qendpoint_closed, endpoint_of_constraint. cbn. exact H. Qed.

Lemma residual_of_constraint_closed : forall bound constraint,
    qconstraint_rhs_closed bound constraint ->
    qendpoint_closed bound (residual_of_constraint constraint).
Proof. intros. unfold qendpoint_closed, residual_of_constraint. cbn. exact H. Qed.

Lemma add_constraint_closed : forall bound constraint state,
    qconstraint_rhs_closed bound constraint ->
    qelim_state_closed bound state ->
    qelim_state_closed bound (add_constraint constraint state).
Proof.
  intros bound [coefficient rhs strict] [residual lower upper] Hconstraint Hstate.
  unfold add_constraint, qelim_state_closed in *. cbn in *.
  destruct Hstate as [Hr [Hl Hu]].
  destruct (Qlt_le_dec coefficient 0); cbn.
  - repeat split; try assumption. constructor.
    + apply endpoint_of_constraint_closed. exact Hconstraint.
    + exact Hl.
  - destruct (Qeq_dec coefficient 0); cbn.
    + repeat split; try assumption. constructor.
      * apply residual_of_constraint_closed. exact Hconstraint.
      * exact Hr.
    + repeat split; try assumption. constructor.
      * apply endpoint_of_constraint_closed. exact Hconstraint.
      * exact Hu.
Qed.

Lemma classify_constraints_closed : forall bound constraints,
    List.Forall (qconstraint_rhs_closed bound) constraints ->
    qelim_state_closed bound (classify_constraints constraints).
Proof.
  intros bound constraints Hclosed. induction Hclosed; cbn.
  - unfold qelim_state_closed, empty_state. cbn. repeat split; constructor.
  - apply add_constraint_closed; assumption.
Qed.

Definition qoutput_atom_closed (bound : nat) (atom : QOutputAtom) : Prop :=
  qterm_closed bound (output_left atom) = true /\
  qterm_closed bound (output_right atom) = true.

Lemma eliminate_state_closed : forall bound state,
    qelim_state_closed bound state ->
    List.Forall (qoutput_atom_closed bound) (eliminate_state state).
Proof.
  intros bound [residual lower upper] [Hr [Hl Hu]].
  unfold eliminate_state. cbn. apply Forall_app. split.
  - rewrite Forall_map. apply Forall_forall. intros endpoint Hin.
    apply Forall_forall with (x := endpoint) in Hr; [|exact Hin].
    unfold qoutput_atom_closed, residual_atom. cbn. split; [reflexivity|exact Hr].
  - unfold pair_atoms. rewrite Forall_flat_map. apply Forall_forall.
    intros low Hlow. apply Forall_forall with (x := low) in Hl; [|exact Hlow].
    rewrite Forall_map. apply Forall_forall. intros high Hhigh.
    apply Forall_forall with (x := high) in Hu; [|exact Hhigh].
    unfold qoutput_atom_closed, pair_atom. cbn. auto.
Qed.

Lemma qoutput_to_affine_closed : forall bound cell,
    List.Forall (qoutput_atom_closed bound) cell ->
    qaffine_conjunction_closed bound (qoutput_conjunction_to_affine cell).
Proof.
  intros bound cell Hclosed. unfold qaffine_conjunction_closed,
    qoutput_conjunction_to_affine. rewrite Forall_map. apply Forall_forall.
  intros atom Hin. apply Forall_forall with (x := atom) in Hclosed; [|exact Hin].
  destruct Hclosed as [Hleft Hright]. unfold qoutput_atom_to_affine.
  destruct (output_strict atom); cbn; rewrite Hleft, Hright; reflexivity.
Qed.

Lemma eliminate_one_closed : forall bound cell,
    qaffine_conjunction_closed (S bound) cell ->
    qaffine_dnf_closed bound
      (qoutput_dnf_to_affine (eliminate_one cell)).
Proof.
  intros bound cell Hclosed. unfold qaffine_dnf_closed,
    qoutput_dnf_to_affine. rewrite Forall_map. apply Forall_forall.
  intros output Houtput. apply qoutput_to_affine_closed.
  unfold eliminate_one in Houtput. cbn in Houtput.
  destruct Houtput as [<-|[]]. apply eliminate_state_closed.
  apply classify_constraints_closed. apply normalize_conjunction_rhs_closed.
  exact Hclosed.
Qed.

Lemma qaffine_dnf_exists_closed : forall bound dnf,
    qaffine_dnf_closed (S bound) dnf ->
    qaffine_dnf_closed bound (qaffine_dnf_exists dnf).
Proof.
  intros bound dnf Hclosed. unfold qaffine_dnf_closed,
    qaffine_dnf_exists in *. rewrite Forall_flat_map. apply Forall_forall.
  intros cell Hin. apply Forall_forall with (x := cell) in Hclosed; [|exact Hin].
  apply eliminate_one_closed. exact Hclosed.
Qed.

Theorem qformula_to_dnf_closed : forall formula bound,
    qformula_closed bound formula = true ->
    qaffine_dnf_closed bound (qformula_to_dnf formula).
Proof.
  intro formula. induction formula; intros bound Hclosed; cbn in *.
  - unfold qaffine_dnf_closed, qaffine_conjunction_closed. cbn.
    repeat constructor.
  - unfold qaffine_dnf_closed. constructor.
  - apply andb_true_iff in Hclosed as [Hleft Hright].
    unfold qaffine_dnf_closed, qaffine_conjunction_closed. cbn.
    constructor.
    + constructor.
      * cbn. rewrite Hleft, Hright. reflexivity.
      * constructor.
        -- cbn. rewrite Hleft, Hright. reflexivity.
        -- constructor.
    + constructor.
  - apply andb_true_iff in Hclosed as [Hleft Hright].
    unfold qaffine_dnf_closed, qaffine_conjunction_closed. cbn.
    constructor.
    + constructor; [cbn; rewrite Hleft, Hright; reflexivity|constructor].
    + constructor.
  - apply andb_true_iff in Hclosed as [Hleft Hright].
    unfold qaffine_dnf_closed, qaffine_conjunction_closed. cbn.
    constructor.
    + constructor; [cbn; rewrite Hleft, Hright; reflexivity|constructor].
    + constructor.
  - apply andb_true_iff in Hclosed as [Hleft Hright].
    apply qaffine_dnf_and_closed; [apply IHformula1|apply IHformula2]; assumption.
  - apply andb_true_iff in Hclosed as [Hleft Hright].
    apply qaffine_dnf_or_closed; [apply IHformula1|apply IHformula2]; assumption.
  - apply qaffine_dnf_neg_closed. apply IHformula. exact Hclosed.
  - apply qaffine_dnf_exists_closed. apply IHformula. exact Hclosed.
  - apply qaffine_dnf_neg_closed. apply qaffine_dnf_exists_closed.
    apply qaffine_dnf_neg_closed. apply IHformula. exact Hclosed.
Qed.

Theorem qdefinable_finite_cells : forall d (C : QSet d),
    QDefinable C ->
    exists cells : list QAffineConjunction,
      forall x : QVec d,
        C x <->
        exists cell, List.In cell cells /\
          qconjunction_semantics (qvec_environment x) cell.
Proof.
  intros d C [formula [_ Hformula]]. exists (qformula_to_dnf formula).
  intro x. rewrite Hformula, qformula_to_dnf_correct. reflexivity.
Qed.
