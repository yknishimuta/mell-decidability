From Coq Require Import List Lia Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Contexts RunOrder.
From Mell.WSVAS Require Import BVASSimulation.

Import ListNotations.

Section LeafIncrements.
Context {d : nat} (system : IBVAS d).

Fixpoint add_source_increments (sources increments : list (NVec d))
    : option (list (NVec d)) :=
  match sources, increments with
  | [], [] => Some []
  | source :: sources', increment :: increments' =>
      match add_source_increments sources' increments' with
      | Some tail => Some (nvec_add source increment :: tail)
      | None => None
      end
  | _, _ => None
  end.

Lemma add_source_increments_length : forall sources increments,
  length sources = length increments ->
  exists shifted,
    add_source_increments sources increments = Some shifted /\
    length shifted = length sources.
Proof.
  induction sources as [|source sources IH]; intros increments Hlength.
  - destruct increments; [exists []; auto|discriminate].
  - destruct increments as [|increment increments]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength.
    destruct (IH increments Hlength) as [shifted [Hshifted Hlen]].
    exists (nvec_add source increment :: shifted). cbn.
    rewrite Hshifted. auto.
Qed.

Lemma add_source_increments_app : forall left_sources right_sources
    left_increments right_increments left_shifted right_shifted,
  add_source_increments left_sources left_increments = Some left_shifted ->
  add_source_increments right_sources right_increments = Some right_shifted ->
  add_source_increments (left_sources ++ right_sources)
    (left_increments ++ right_increments) = Some (left_shifted ++ right_shifted).
Proof.
  induction left_sources as [|source sources IH];
    intros right_sources left_increments right_increments
      left_shifted right_shifted Hleft Hright.
  - destruct left_increments; cbn in Hleft; [inversion Hleft; subst|discriminate].
    exact Hright.
  - destruct left_increments as [|increment increments]; cbn in Hleft;
      [discriminate|].
    destruct (add_source_increments sources increments) eqn:Htail;
      [|discriminate].
    inversion Hleft; subst. cbn. rewrite (IH _ _ _ _ _ Htail Hright).
    reflexivity.
Qed.

Lemma nvec_rsum_add_source_increments : forall sources increments shifted,
  add_source_increments sources increments = Some shifted ->
  nvec_rsum shifted =
    nvec_add (nvec_rsum sources) (nvec_rsum increments).
Proof.
  induction sources as [|source sources IH]; intros increments shifted Hshifted.
  - destruct increments; cbn in Hshifted; inversion Hshifted; subst.
    cbn. symmetry. apply nvec_add_zero_left.
  - destruct increments as [|increment increments]; cbn in Hshifted;
      [discriminate|].
    destruct (add_source_increments sources increments) eqn:Htail;
      [|discriminate].
    inversion Hshifted; subst. cbn. rewrite (IH _ _ Htail).
    apply (proj1 (Vector.eq_nth_iff nat d _ _)).
    intros index index' Heq; subst index'. unfold nvec_add.
    repeat rewrite (Vector.nth_map2 Nat.add _ _ index index index
      eq_refl eq_refl). lia.
Qed.

Lemma apply_action_total_shift : forall (action : Action d)
    (old_children new_children : list (NVec d))
    (old_target delta : NVec d),
  length old_children = length new_children ->
  nvec_sum new_children = nvec_add (nvec_sum old_children) delta ->
  apply_action action old_children = Some old_target ->
  apply_action action new_children = Some (nvec_add old_target delta).
Proof.
  intros action old_children new_children old_target delta Hlength Hsum Happly.
  unfold apply_action in Happly |- *.
  destruct (Nat.eqb (length old_children) (action_arity action)) eqn:Harity;
    [|discriminate].
  rewrite <- Hlength, Harity. unfold add_displacement in Happly |- *.
  assert (Hold :
    zvec_add (action_offset action) (nvec_to_zvec (nvec_sum old_children)) =
      nvec_to_zvec old_target).
  { apply (proj1 (Vector.eq_nth_iff Z d _ _)).
    intros index index' Heq; subst index'. unfold nvec_to_zvec.
    rewrite (Vector.nth_map Z.of_nat old_target index index eq_refl).
    eapply zvec_to_nvec_sound; exact Happly. }
  rewrite Hsum, nvec_to_zvec_add, zvec_add_assoc, Hold,
    <- nvec_to_zvec_add. apply zvec_to_nvec_of_nvec.
Qed.

Inductive LeafIncrementsRun :
    IRun d -> list (NVec d) -> IRun d -> Prop :=
| leaf_increments_leaf : forall source increment,
    LeafIncrementsRun (irun_leaf source) [increment]
      (irun_leaf (nvec_add source increment))
| leaf_increments_node : forall action children target increments
      shifted_children,
    LeafIncrementsRuns children increments shifted_children ->
    LeafIncrementsRun (irun_node action children target) increments
      (irun_node action shifted_children
        (nvec_add target (nvec_rsum increments)))
with LeafIncrementsRuns :
    IRuns d -> list (NVec d) -> IRuns d -> Prop :=
| leaf_increments_nil : LeafIncrementsRuns iruns_nil [] iruns_nil
| leaf_increments_cons : forall run runs run_increments runs_increments
      shifted_run shifted_runs,
    LeafIncrementsRun run run_increments shifted_run ->
    LeafIncrementsRuns runs runs_increments shifted_runs ->
    LeafIncrementsRuns (iruns_cons run runs)
      (run_increments ++ runs_increments)
      (iruns_cons shifted_run shifted_runs).

Scheme LeafIncrementsRun_ind' := Induction for LeafIncrementsRun Sort Prop
with LeafIncrementsRuns_ind' := Induction for LeafIncrementsRuns Sort Prop.
Combined Scheme LeafIncrements_mutind
  from LeafIncrementsRun_ind', LeafIncrementsRuns_ind'.

Combined Scheme ValidFreeRunRuns_mutind
  from ValidFreeIRun_ind', ValidFreeIRuns_ind'.

Lemma leaf_increments_properties :
  (forall run increments shifted,
    LeafIncrementsRun run increments shifted ->
    (exists sources,
      add_source_increments (free_irun_sources run) increments = Some sources /\
      free_irun_sources shifted = sources) /\
    irun_target shifted =
      nvec_add (irun_target run) (nvec_rsum increments)) /\
  (forall runs increments shifted,
    LeafIncrementsRuns runs increments shifted ->
    (exists sources,
      add_source_increments (free_iruns_sources runs) increments = Some sources /\
      free_iruns_sources shifted = sources) /\
    nvec_rsum (iruns_targets shifted) =
      nvec_add (nvec_rsum (iruns_targets runs)) (nvec_rsum increments)).
Proof.
  apply LeafIncrements_mutind; intros; cbn.
  - split.
    + exists [nvec_add source increment]. auto.
    + rewrite nvec_add_zero_right. reflexivity.
  - destruct H as [Hsources Htargets]. split; [exact Hsources|reflexivity].
  - split.
    + exists []; auto.
    + cbn. symmetry. apply nvec_add_zero_left.
  - destruct H as [[run_sources [Hleft Hrun_sources]] Hrun_target].
    destruct H0 as [[runs_sources [Hright Hruns_sources]] Hruns_target]. split.
    + exists (run_sources ++ runs_sources). split.
      * now apply add_source_increments_app.
      * cbn. now rewrite Hrun_sources, Hruns_sources.
    + cbn. rewrite Hrun_target, Hruns_target, nvec_rsum_app.
      apply (proj1 (Vector.eq_nth_iff nat d _ _)).
      intros index index' Heq; subst index'. unfold nvec_add.
      repeat rewrite (Vector.nth_map2 Nat.add _ _ index index index
        eq_refl eq_refl). lia.
Qed.

Lemma leaf_increments_runs_target_length : forall runs increments shifted,
  LeafIncrementsRuns runs increments shifted ->
  length (iruns_targets runs) = length (iruns_targets shifted).
Proof. intros runs increments shifted H; induction H; cbn; congruence. Qed.

Lemma leaf_increments_valid :
  (forall run, ValidFreeIRun system run -> forall increments shifted,
    LeafIncrementsRun run increments shifted ->
    ValidFreeIRun system shifted) /\
  (forall runs, ValidFreeIRuns system runs -> forall increments shifted,
    LeafIncrementsRuns runs increments shifted ->
    ValidFreeIRuns system shifted).
Proof.
  apply ValidFreeRunRuns_mutind.
  - intros value increments shifted Hshift. inversion Hshift; subst. constructor.
  - intros action children target Haction Hchildren IHchildren Happly
      increments shifted Hshift.
    inversion Hshift; subst. constructor; [exact Haction|eauto|].
    destruct (proj2 leaf_increments_properties _ _ _ H4) as [_ Hsum].
    eapply (apply_action_total_shift action (iruns_targets children)
      (iruns_targets shifted_children) target (nvec_rsum increments)).
    + now apply leaf_increments_runs_target_length with (increments := increments).
    + repeat rewrite nvec_sum_rsum. exact Hsum.
    + exact Happly.
  - intros increments shifted Hshift. inversion Hshift; constructor.
  - intros run runs Hrun IHrun Hruns IHruns increments shifted Hshift.
    inversion Hshift; subst. constructor; eauto.
Qed.

Lemma leaf_increments_exists :
  (forall run, ValidFreeIRun system run -> forall increments,
    length increments = length (free_irun_sources run) ->
    exists shifted, LeafIncrementsRun run increments shifted) /\
  (forall runs, ValidFreeIRuns system runs -> forall increments,
    length increments = length (free_iruns_sources runs) ->
    exists shifted, LeafIncrementsRuns runs increments shifted).
Proof.
  apply ValidFreeRunRuns_mutind.
  - intros value increments Hlength.
    destruct increments as [|increment tail]; cbn in Hlength;
      [discriminate|]. destruct tail; [|discriminate].
    exists (irun_leaf (nvec_add value increment)). constructor.
  - intros action children target Haction Hchildren IHchildren Happly
      increments Hlength.
    destruct (IHchildren increments Hlength) as [shifted Hshifted].
    exists (irun_node action shifted
      (nvec_add target (nvec_rsum increments))). constructor. exact Hshifted.
  - intros increments Hlength. destruct increments; cbn in Hlength;
      [exists iruns_nil; constructor|discriminate].
  - intros run runs Hrun IHrun Hruns IHruns increments Hlength.
    cbn in Hlength. rewrite app_length in Hlength.
    set (left := firstn (length (free_irun_sources run)) increments).
    set (right := skipn (length (free_irun_sources run)) increments).
    assert (Hsplit : increments = left ++ right).
    { unfold left, right. symmetry. apply firstn_skipn. }
    assert (Hleft : length left = length (free_irun_sources run)).
    { unfold left. rewrite firstn_length. lia. }
    assert (Hright : length right = length (free_iruns_sources runs)).
    { unfold right. rewrite skipn_length. lia. }
    destruct (IHrun left Hleft) as [shifted_run Hshifted_run].
    destruct (IHruns right Hright) as [shifted_runs Hshifted_runs].
    exists (iruns_cons shifted_run shifted_runs). rewrite Hsplit.
    now constructor.
Qed.

Theorem fact_3_2_all_leaf_increments : forall run increments,
  ValidFreeIRun system run ->
  length increments = length (free_irun_sources run) ->
  exists shifted sources,
    ValidFreeIRun system shifted /\
    LeafIncrementsRun run increments shifted /\
    add_source_increments (free_irun_sources run) increments =
      Some sources /\
    free_irun_sources shifted = sources /\
    irun_target shifted =
      nvec_add (irun_target run) (nvec_rsum increments).
Proof.
  intros run increments Hvalid Hlength.
  destruct (proj1 leaf_increments_exists run Hvalid increments Hlength)
    as [shifted Hshifted].
  destruct (add_source_increments_length (free_irun_sources run) increments
    (eq_sym Hlength))
    as [sources [Hsources _]].
  exists shifted, sources. repeat split.
  - eapply (proj1 leaf_increments_valid); eauto.
  - exact Hshifted.
  - exact Hsources.
  - destruct (proj1 leaf_increments_properties _ _ _ Hshifted)
      as [[sources' [Hsources' Heq]] _].
    rewrite Hsources in Hsources'. inversion Hsources'. now subst.
  - exact (proj2 (proj1 leaf_increments_properties _ _ _ Hshifted)).
Qed.

End LeafIncrements.
