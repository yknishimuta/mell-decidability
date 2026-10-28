From Coq Require Import Lia List QArith Qabs Qround Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Contexts RunOrder Amalgamation.
From Mell.Geometry Require Import ClosedLinearization ClosedLinearizationL2
  Cone FaceStrippingLemma610 LatticeGordanInterface LatticeGordanMain
  LatticeGordanV MathCompBridge Periodic QConeCore RationalClosure
  RationalDefinability.
From Mell.Order Require Import PeriodicOrder.
From Mell.Semilinear Require Import Presentation LinearEquations.
From Mell.Separator Require Import TransformerPeriod.
From Mell.VAS Require Import AlmostSemilinearProjection AsymptoticRelation
  Intraproductions PeriodicIntersection RelationCone.

Import ListNotations.
Module StdVector := Coq.Vectors.Vector.

(** A directed initialized run carries an explicitly finitely generated
    rational cone.  The last field records the paper's requirement that the
    cone lie in the nonnegative orthant. *)
Record DirectedIRun {d} (system : IBVAS d) : Type := {
  directed_root : IRun d;
  directed_root_valid : ValidIRun system directed_root;
  directed_generators : list (QVec d);
  directed_cone_nonnegative :
    forall point, qcone_generated directed_generators point ->
    forall index, 0 <= point index
}.

Arguments directed_root {d system} _.
Arguments directed_root_valid {d system} _.
Arguments directed_generators {d system} _.

Lemma nvec_to_qvec_zero_directed : forall d,
    qvec_eq (nvec_to_qvec (nvec_zero d)) (qvec_zero d).
Proof.
  intros d index. unfold nvec_to_qvec, nvec_zero, qvec_zero, q_of_nat.
  rewrite (StdVector.const_nth nat 0%nat d index). reflexivity.
Qed.

Lemma nvec_to_qvec_add_directed : forall d (left right : NVec d),
    qvec_eq (nvec_to_qvec (nvec_add left right))
      (qvec_add (nvec_to_qvec left) (nvec_to_qvec right)).
Proof.
  intros d left right index. unfold nvec_to_qvec, nvec_add, qvec_add, q_of_nat.
  rewrite (StdVector.nth_map2 _ _ _ index index index eq_refl eq_refl),
    Nat2Z.inj_add, inject_Z_plus. reflexivity.
Qed.

Definition DirectedCone {d} {system : IBVAS d}
    (directed : DirectedIRun system) : QSet d :=
  qcone_generated (directed_generators directed).

Definition DirectedOffset {d} {system : IBVAS d}
    (directed : DirectedIRun system) (offset : NVec d) : Prop :=
  IRunPeriod system (directed_root directed) offset /\
  DirectedCone directed (nvec_to_qvec offset).

Definition DirectedPeriod {d} {system : IBVAS d}
    (directed : DirectedIRun system) : ZSet d :=
  NSetAsZ (DirectedOffset directed).

Definition DirectedClosedPeriod {d} {system : IBVAS d}
    (directed : DirectedIRun system) : ZSet d :=
  ClosedLinearization (DirectedPeriod directed).

Definition DirectedRunMember {d} {system : IBVAS d}
    (directed : DirectedIRun system) (run : IRun d) : Prop :=
  ValidIRun system run /\
  exists offset,
    IRunLe (directed_root directed) run /\
    irun_target run =
      nvec_add (irun_target (directed_root directed)) offset /\
    DirectedCone directed (nvec_to_qvec offset).

Lemma directed_cone_polyhedral : forall d (system : IBVAS d)
    (directed : DirectedIRun system),
    RationalPolyhedralCone (DirectedCone directed).
Proof.
  intros. apply qcone_generated_is_rational_polyhedral_cone.
Qed.

Lemma directed_integer_cone_periodic : forall d (system : IBVAS d)
    (directed : DirectedIRun system),
    Periodic (fun value : ZVec d =>
      DirectedCone directed (zvec_to_qvec value)).
Proof.
  intros. apply rational_polyhedral_integer_points_periodic.
  apply directed_cone_polyhedral.
Qed.

Lemma directed_integer_cone_finitely_generated : forall d
    (system : IBVAS d) (directed : DirectedIRun system),
    FinitelyGeneratedPeriodic (fun value : ZVec d =>
      DirectedCone directed (zvec_to_qvec value)).
Proof.
  intros d system directed. unfold DirectedCone.
  apply integer_points_vcone_finitely_generated.
Qed.

Lemma directed_integer_cone_asymptotically_definable : forall d
    (system : IBVAS d) (directed : DirectedIRun system),
    AsymptoticallyDefinable (fun value : ZVec d =>
      DirectedCone directed (zvec_to_qvec value)).
Proof.
  intros d system directed.
  apply rational_polyhedral_cone_qdefinable.
  apply finitely_generated_period_cone_polyhedral.
  - apply directed_integer_cone_periodic.
  - apply directed_integer_cone_finitely_generated.
Qed.

Lemma directed_offset_periodic : forall d (system : IBVAS d)
    (directed : DirectedIRun system),
    PeriodicNSet (DirectedOffset directed).
Proof.
  intros d system directed.
  destruct (irun_period_periodic d system (directed_root directed)
    (directed_root_valid directed)) as [Hzero Hadd]. split.
  - split; [exact Hzero|]. unfold DirectedCone.
    apply (proj2 (qcone_generated_qvec_ext d _ _ _
      (nvec_to_qvec_zero_directed d))).
    apply qcone_generated_zero.
  - intros left right [Hleft_period Hleft_cone]
      [Hright_period Hright_cone]. split.
    + now apply Hadd.
    + unfold DirectedCone in *.
      apply (proj2 (qcone_generated_qvec_ext d _ _ _
        (nvec_to_qvec_add_directed d left right))).
      apply qcone_generated_add; assumption.
Qed.

Lemma directed_period_periodic : forall d (system : IBVAS d)
    (directed : DirectedIRun system),
    Periodic (DirectedPeriod directed).
Proof.
  intros. apply periodic_nset_as_z, directed_offset_periodic.
Qed.

Lemma directed_period_asymptotically_definable : forall d
    (system : IBVAS d) (directed : DirectedIRun system),
    AsymptoticallyDefinable (DirectedPeriod directed).
Proof.
  intros d system directed.
  pose proof (lemma_4_11_irun_period_asymptotically_definable d system
    (directed_root directed) (directed_root_valid directed)) as Hroot.
  eapply (@qdefinable_congr d
    (Cone (fun integer =>
      NSetAsZ (IRunPeriod system (directed_root directed)) integer /\
      DirectedCone directed (zvec_to_qvec integer)))
    (Cone (DirectedPeriod directed))).
  - intro point. apply cone_same_generators. intro integer.
    unfold DirectedPeriod, DirectedOffset. split.
    + intros [[natural [E Hperiod]] Hcone]. exists natural. split; [exact E|].
      split; [exact Hperiod|]. subst integer.
      apply (proj1 (qcone_generated_qvec_ext d _ _ _
        (nvec_zvec_qvec_commute d natural))). exact Hcone.
    + intros [natural [E [Hperiod Hcone]]]. split.
      * now exists natural.
      * subst integer.
        apply (proj2 (qcone_generated_qvec_ext d _ _ _
          (nvec_zvec_qvec_commute d natural))). exact Hcone.
  - apply lemma_6_2_asymptotically_definable_intersection.
    + apply periodic_nset_as_z. exact (proj1 Hroot).
    + apply directed_integer_cone_periodic.
    + exact (proj2 Hroot).
    + apply directed_integer_cone_asymptotically_definable.
Qed.

Lemma directed_period_nonnegative : forall d (system : IBVAS d)
    (directed : DirectedIRun system),
    NonnegativeSet (DirectedPeriod directed).
Proof.
  intros d system directed integer [natural [-> _]] index.
  unfold nvec_to_zvec.
  rewrite (StdVector.nth_map _ _ index index eq_refl). lia.
Qed.

Lemma rational_polyhedral_integer_points_cone : forall d (cone : QSet d),
    RationalPolyhedralCone cone -> forall point,
    Cone (fun integer : ZVec d => cone (zvec_to_qvec integer)) point <->
    cone point.
Proof.
  intros d cone [generators Hgenerators] point. split.
  - intros [generated [Hgenerated Hpoint]].
    assert (Hlift : forall generated,
        ConeGen (fun integer : ZVec d => cone (zvec_to_qvec integer)) generated ->
        qcone_generated generators generated).
    { intros generated' Hgenerated'. induction Hgenerated'.
      - apply qcone_generated_zero.
      - apply qcone_generated_add.
        + apply qcone_generated_scale; [exact H|].
          now apply (proj1 (Hgenerators (zvec_to_qvec value))).
        + exact IHHgenerated'. }
    apply (proj2 (Hgenerators point)).
    apply (proj2 (qcone_generated_qvec_ext d generators point generated Hpoint)).
    now apply Hlift.
  - intro Hpoint.
    destruct (integerize_vcone d generators) as [integers Hintegers].
    apply qcone_mapped_generators_in_period_cone with (generators := integers).
    + intros integer Hinteger. apply (proj2 (Hgenerators _)).
      apply (proj2 (Hintegers _)).
      apply qcone_generated_generator. now apply in_map.
    + apply (proj1 (Hintegers point)), (proj1 (Hgenerators point)), Hpoint.
Qed.

Lemma directed_period_cone_iff : forall d (system : IBVAS d)
    (directed : DirectedIRun system) point,
    Cone (DirectedPeriod directed) point <->
    Cone (NSetAsZ (IRunPeriod system (directed_root directed))) point /\
    DirectedCone directed point.
Proof.
  intros d system directed point.
  transitivity (Cone (fun integer : ZVec d =>
    NSetAsZ (IRunPeriod system (directed_root directed)) integer /\
    DirectedCone directed (zvec_to_qvec integer)) point).
  - apply cone_same_generators. intro integer. unfold DirectedPeriod,
      DirectedOffset. split.
    + intros [natural [E [Hperiod Hcone]]]. split.
      * now exists natural.
      * subst integer. apply (proj2 (qcone_generated_qvec_ext d _ _ _
          (nvec_zvec_qvec_commute d natural))). exact Hcone.
    + intros [[natural [E Hperiod]] Hcone]. exists natural. split; [exact E|].
      split; [exact Hperiod|]. subst integer.
      apply (proj1 (qcone_generated_qvec_ext d _ _ _
        (nvec_zvec_qvec_commute d natural))). exact Hcone.
  - rewrite periodic_cone_intersection.
    + rewrite rational_polyhedral_integer_points_cone.
      * reflexivity.
      * apply directed_cone_polyhedral.
    + apply periodic_nset_as_z.
      apply irun_period_periodic, directed_root_valid.
    + apply directed_integer_cone_periodic.
Qed.

Theorem lemma_3_12_directed_closed_period_finitely_generated : forall d
    (system : IBVAS d) (directed : DirectedIRun system),
    FinitelyGeneratedPeriodic (DirectedClosedPeriod directed).
Proof.
  intros d system directed. unfold DirectedClosedPeriod.
  apply closed_linearization_finitely_generated.
  - apply directed_period_periodic.
  - apply directed_period_nonnegative.
  - apply directed_period_asymptotically_definable.
Qed.

Theorem directed_run_targets : forall d (system : IBVAS d)
    (directed : DirectedIRun system) target,
    (exists run, DirectedRunMember directed run /\ irun_target run = target) <->
    exists offset,
      DirectedOffset directed offset /\
      target = nvec_add (irun_target (directed_root directed)) offset.
Proof.
  intros d system directed target. split.
  - intros [run [[Hvalid [offset [Hle [Htarget Hcone]]]] Hfinal]].
    subst target.
    exists offset. split; [split|]; auto.
    exists run. auto.
  - intros [offset [[Hperiod Hcone] Htarget]].
    destruct Hperiod as [run [Hvalid [Hle Hrun_target]]].
    exists run. split.
    + split; [exact Hvalid|]. exists offset. auto.
    + now rewrite Hrun_target, Htarget.
Qed.

(** A concrete occurrence, rather than mere [IRunLe], is witnessed by the
    one-hole context around it.  Different occurrences of extensionally equal
    subruns may therefore use different witnesses. *)
Definition IRunOccurrence {d} (subrun whole : IRun d) : Prop :=
  exists context : IContext d, whole = context_plug context subrun.

Definition DirectedIRunEdge {d} {system : IBVAS d}
    (source target : DirectedIRun system) : Prop :=
  exists source_run target_run,
    DirectedRunMember source source_run /\
    DirectedRunMember target target_run /\
    IRunOccurrence source_run target_run.

Definition DirectedConeIncluded {d} {system : IBVAS d}
    (source target : DirectedIRun system) : Prop :=
  forall point, DirectedCone source point -> DirectedCone target point.

Lemma irun_occurrence_lift : forall d (system : IBVAS d)
    (subrun replacement whole : IRun d) delta,
    ValidIRun system whole ->
    ValidIRun system replacement ->
    IRunOccurrence subrun whole ->
    IRunLe subrun replacement ->
    irun_target replacement = nvec_add (irun_target subrun) delta ->
    exists lifted,
      ValidIRun system lifted /\
      IRunLe whole lifted /\
      irun_target lifted = nvec_add (irun_target whole) delta /\
      IRunOccurrence replacement lifted.
Proof.
  intros d system subrun replacement whole delta Hwhole Hreplacement
    [context ->] Hle Hdelta.
  destruct (context_lift d system context subrun replacement delta
    Hwhole Hreplacement Hle Hdelta) as [Hvalid [Horder Htarget]].
  exists (context_plug (context_add delta context) replacement).
  split; [exact Hvalid|]. split; [exact Horder|].
  split; [exact Htarget|].
  exists (context_add delta context). reflexivity.
Qed.

Lemma irun_period_translate_along_occurrence : forall d (system : IBVAS d)
    (source_root target_root source_run target_run : IRun d)
    source_offset target_offset,
    ValidIRun system source_root ->
    ValidIRun system source_run ->
    ValidIRun system target_run ->
    IRunLe source_root source_run ->
    IRunLe target_root target_run ->
    IRunOccurrence source_run target_run ->
    irun_target source_run =
      nvec_add (irun_target source_root) source_offset ->
    irun_target target_run =
      nvec_add (irun_target target_root) target_offset ->
    forall increment,
      IRunPeriod system source_root increment ->
      IRunPeriod system target_root (nvec_add target_offset increment).
Proof.
  intros d system source_root target_root source_run target_run
    source_offset target_offset Hroot Hsource Htarget Hroot_source
    Htarget_root Hocc Hsource_target Htarget_target increment
    [extension [Hextension [Hroot_extension Hextension_target]]].
  destruct (run_amalgamation d system source_root source_run extension
    Hroot Hsource Hextension Hroot_source Hroot_extension) as
    [source' [Hsource' [Hsource_order [_ Hexact]]]].
  assert (Hsource'_target :
      irun_target source' = nvec_add (irun_target source_run) increment).
  { eapply nvec_exact_delta; eauto. }
  destruct (irun_occurrence_lift d system source_run source' target_run
    increment Htarget Hsource' Hocc Hsource_order Hsource'_target) as
    [target' [Htarget' [Htarget_order [Htarget'_target _]]]].
  exists target'. split; [exact Htarget'|]. split.
  - exact (irun_le_trans d target_root target_run target'
      Htarget_root Htarget_order).
  - rewrite Htarget'_target, Htarget_target, <- nvec_add_assoc. reflexivity.
Qed.

Theorem directed_edge_translated_offset_inclusion : forall d
    (system : IBVAS d) (source target : DirectedIRun system),
    DirectedIRunEdge source target ->
    DirectedConeIncluded source target ->
    exists translation,
      DirectedOffset target translation /\
      forall offset,
        DirectedOffset source offset ->
        DirectedOffset target (nvec_add translation offset).
Proof.
  intros d system source target
    [source_run [target_run [Hsource_member [Htarget_member Hocc]]]] Hcones.
  destruct Hsource_member as [Hsource_valid
    [source_offset [Hsource_order [Hsource_target Hsource_cone]]]].
  destruct Htarget_member as [Htarget_valid
    [target_offset [Htarget_order [Htarget_target Htarget_cone]]]].
  exists target_offset. split.
  - split.
    + exists target_run. split; [exact Htarget_valid|].
      split; [exact Htarget_order|exact Htarget_target].
    + exact Htarget_cone.
  - intros offset [Hperiod Hcone]. split.
    + eapply (irun_period_translate_along_occurrence d system
        (directed_root source) (directed_root target)
        source_run target_run source_offset target_offset);
        eauto using directed_root_valid.
    + apply (proj2 (qcone_generated_qvec_ext d _ _ _
        (nvec_to_qvec_add_directed d target_offset offset))).
      apply qcone_generated_add; [exact Htarget_cone|].
      apply Hcones. exact Hcone.
Qed.

Lemma nvec_to_zvec_add_directed : forall d (left right : NVec d),
    nvec_to_zvec (nvec_add left right) =
      zvec_add (nvec_to_zvec left) (nvec_to_zvec right).
Proof. intros. apply nvec_to_zvec_add. Qed.

Lemma translated_difference_inclusion : forall d
    (left right : NVec d -> Prop) translation,
    (forall value, left value -> right (nvec_add translation value)) ->
    forall difference,
      Difference (NSetAsZ left) difference ->
      Difference (NSetAsZ right) difference.
Proof.
  intros d left right translation Htranslate difference
    [left_z [right_z [[left_n [-> Hleft]]
      [[right_n [-> Hright]] ->]]]].
  exists (nvec_to_zvec (nvec_add translation left_n)),
    (nvec_to_zvec (nvec_add translation right_n)).
  split.
  - exists (nvec_add translation left_n). split; [reflexivity|].
    now apply Htranslate.
  - split.
    + exists (nvec_add translation right_n). split; [reflexivity|].
      now apply Htranslate.
    + rewrite !nvec_to_zvec_add_directed.
      apply (proj1 (StdVector.eq_nth_iff Z d _ _)).
      intros index index' Hindex. subst index'.
      unfold zvec_sub, zvec_add.
      repeat rewrite (StdVector.nth_map2 _ _ _ index index index eq_refl eq_refl).
      lia.
Qed.

Fixpoint nvec_total {d} (value : NVec d) : nat :=
  match value with
  | @StdVector.nil _ => 0%nat
  | @StdVector.cons _ head _ tail => (head + nvec_total tail)%nat
  end.

Lemma nvec_nth_le_total : forall d (value : NVec d) (index : Fin.t d),
    (StdVector.nth value index <= nvec_total value)%nat.
Proof.
  intros d value. induction value as [|head d tail IH].
  - intro index. exact (Fin.case0 (fun index =>
      (StdVector.nth (StdVector.nil nat) index <=
        nvec_total (StdVector.nil nat))%nat) index).
  - intro index. refine (Fin.caseS' index (fun index =>
      (StdVector.nth (StdVector.cons nat head d tail) index <=
        nvec_total (StdVector.cons nat head d tail))%nat) _ _).
    + cbn. lia.
    + intro position. cbn. specialize (IH position). lia.
Qed.

Lemma rational_vanishing_denominator : forall bound delta : Q,
    0 <= bound -> 0 < delta ->
    exists denominator : nat,
      (0 < denominator)%nat /\ bound / q_of_nat denominator < delta.
Proof.
  intros bound delta Hbound Hdelta.
  set (ceiling := Qceiling (bound / delta)).
  assert (Hratio : 0 <= bound / delta).
  { apply Qmult_le_0_compat; [exact Hbound|].
    apply Qlt_le_weak, Qinv_lt_0_compat, Hdelta. }
  assert (Hceiling : (0 <= ceiling)%Z).
  { rewrite Zle_Qle.
    eapply Qle_trans; [exact Hratio|]. apply Qle_ceiling. }
  exists (S (Z.to_nat ceiling)). split; [lia|].
  assert (Hnat : Z.of_nat (S (Z.to_nat ceiling)) = (ceiling + 1)%Z).
  { rewrite Nat2Z.inj_succ, Z2Nat.id by exact Hceiling. lia. }
  assert (Hratio_lt : bound / delta < q_of_nat (S (Z.to_nat ceiling))).
  { unfold q_of_nat. rewrite Hnat.
    eapply Qle_lt_trans; [apply Qle_ceiling|].
    rewrite inject_Z_plus. cbn. change (inject_Z ceiling < inject_Z ceiling + 1).
    assert (Hstep : inject_Z ceiling + 0 < inject_Z ceiling + 1).
    { apply (proj2 (Qplus_lt_r 0 1 (inject_Z ceiling))). reflexivity. }
    setoid_replace (inject_Z ceiling + 0) with (inject_Z ceiling) in Hstep
      by ring.
    exact Hstep. }
  assert (Hden_positive : 0 < q_of_nat (S (Z.to_nat ceiling))).
  { unfold q_of_nat. change (inject_Z 0 < inject_Z (Z.of_nat (S (Z.to_nat ceiling)))).
    rewrite <- Zlt_Qlt. lia. }
  apply (proj2 (Qmult_lt_l _ _ delta Hdelta)) in Hratio_lt.
  setoid_replace (delta * (bound / delta)) with bound in Hratio_lt by field.
  setoid_replace (delta * q_of_nat (S (Z.to_nat ceiling))) with
      (q_of_nat (S (Z.to_nat ceiling)) * delta) in Hratio_lt by ring.
  apply (proj1 (Qmult_lt_r _ _ (q_of_nat (S (Z.to_nat ceiling)))
    Hden_positive)).
  setoid_replace ((bound / q_of_nat (S (Z.to_nat ceiling))) *
      q_of_nat (S (Z.to_nat ceiling))) with bound by field.
  setoid_replace (delta * q_of_nat (S (Z.to_nat ceiling))) with
      (q_of_nat (S (Z.to_nat ceiling)) * delta) by ring.
  exact Hratio_lt.
  - intro Hzero. apply (Qlt_not_eq _ _ Hden_positive).
    symmetry. exact Hzero.
  - intro Hzero. apply (Qlt_not_eq _ _ Hdelta).
    symmetry. exact Hzero.
Qed.

Lemma periodic_nset_scale : forall d (set : NVec d -> Prop),
    PeriodicNSet set -> forall coefficient value,
      set value -> set (nvec_scale coefficient value).
Proof.
  intros d set [Hzero Hadd] coefficient. induction coefficient as [|coefficient IH];
    intro value; intro Hvalue.
  - rewrite nvec_scale_zero. exact Hzero.
  - rewrite nvec_scale_succ. apply Hadd; [exact Hvalue|now apply IH].
Qed.

Lemma q_of_nat_mul_directed : forall left right,
    q_of_nat (left * right) == q_of_nat left * q_of_nat right.
Proof.
  intros. unfold q_of_nat. rewrite Nat2Z.inj_mul, inject_Z_mult. reflexivity.
Qed.

Lemma q_of_nat_nonnegative_directed : forall value,
    0 <= q_of_nat value.
Proof.
  intro value. unfold q_of_nat. change (inject_Z 0 <= inject_Z (Z.of_nat value)).
  rewrite <- Zle_Qle. lia.
Qed.

Lemma q_of_nat_positive_directed : forall value,
    (0 < value)%nat -> 0 < q_of_nat value.
Proof.
  intros value Hvalue. unfold q_of_nat.
  change (inject_Z 0 < inject_Z (Z.of_nat value)).
  rewrite <- Zlt_Qlt. lia.
Qed.

Lemma qinv_product_cancel_right : forall left right : Q,
    ~ left == 0 -> ~ right == 0 ->
    / left == / (left * right) * right.
Proof.
  intros left right Hleft Hright.
  field. split; assumption.
Qed.

Lemma nvec_to_qvec_scale_directed : forall d coefficient (value : NVec d),
    qvec_eq (nvec_to_qvec (nvec_scale coefficient value))
      (qvec_scale (q_of_nat coefficient) (nvec_to_qvec value)).
Proof.
  intros d coefficient value index.
  unfold nvec_to_qvec, nvec_scale, qvec_scale.
  rewrite (StdVector.nth_map _ _ index index eq_refl),
    q_of_nat_mul_directed. reflexivity.
Qed.

Lemma translated_period_cone_closure : forall d
    (left right : NVec d -> Prop) translation,
    PeriodicNSet left ->
    (forall value, left value -> right (nvec_add translation value)) ->
    forall point,
      Cone (NSetAsZ left) point ->
      QClosure (Cone (NSetAsZ right)) point.
Proof.
  intros d left right translation Hleft_periodic Htranslate point Hcone
    delta Hdelta.
  destruct (proj1 (periodic_cone_positive_multiple_iff d
    (NSetAsZ left) point (periodic_nset_as_z d left Hleft_periodic)) Hcone)
    as [multiplier [integer_point
      [Hmultiplier [Hinteger Hmultiple]]]].
  destruct Hinteger as [period [-> Hperiod]].
  destruct (rational_vanishing_denominator
    (q_of_nat (nvec_total translation)) delta
    (q_of_nat_nonnegative_directed _) Hdelta) as
    [replicas [Hreplicas Hsmall]].
  set (translated := nvec_add translation (nvec_scale replicas period)).
  set (coefficient := /
    (q_of_nat (multiplier * replicas))).
  set (approximant := qvec_scale coefficient (nvec_to_qvec translated)).
  exists approximant. split.
  - unfold approximant.
    apply (cone_closed_scale (Cone (NSetAsZ right))
      (cone_is_cone d (NSetAsZ right))).
    + unfold coefficient. apply Qlt_le_weak, Qinv_lt_0_compat.
      apply q_of_nat_positive_directed. nia.
    + apply (proj1 (cone_qvec_extensional d (NSetAsZ right) _ _
        (nvec_zvec_qvec_commute d translated))).
      apply cone_contains_source. exists translated. split; [reflexivity|].
      unfold translated. apply Htranslate.
      now apply periodic_nset_scale.
  - intro index.
    assert (Hcoordinate :
        q_of_nat multiplier * point index ==
        nvec_to_qvec period index).
    { transitivity (zvec_to_qvec (nvec_to_zvec period) index).
      - apply Hmultiple.
      - apply nvec_zvec_qvec_commute. }
    assert (Htranslation_bound :
        (StdVector.nth translation index <= nvec_total translation)%nat).
    { apply nvec_nth_le_total. }
    assert (Hcoordinate_nonnegative :
        0 <= nvec_to_qvec translation index).
    { apply q_of_nat_nonnegative_directed. }
    assert (Hden_positive : 0 < q_of_nat (multiplier * replicas)).
    { apply q_of_nat_positive_directed. nia. }
    assert (Hcoordinate_small :
        nvec_to_qvec translation index /
          q_of_nat (multiplier * replicas) < delta).
    {
      eapply Qle_lt_trans; [|exact Hsmall].
      apply (proj1 (Qmult_le_r _ _ (q_of_nat (multiplier * replicas))
        Hden_positive)).
      setoid_replace ((nvec_to_qvec translation index /
          q_of_nat (multiplier * replicas)) *
          q_of_nat (multiplier * replicas)) with
        (nvec_to_qvec translation index) by field.
      setoid_replace ((q_of_nat (nvec_total translation) / q_of_nat replicas) *
          q_of_nat (multiplier * replicas)) with
        (q_of_nat (nvec_total translation) * q_of_nat multiplier) by
        (rewrite q_of_nat_mul_directed; field).
      eapply Qle_trans with (y := q_of_nat (nvec_total translation)).
      - unfold nvec_to_qvec, q_of_nat.
        rewrite <- Zle_Qle. lia.
      - setoid_replace (q_of_nat (nvec_total translation)) with
          (q_of_nat (nvec_total translation) * 1) at 1 by ring.
        setoid_replace (q_of_nat (nvec_total translation) * 1) with
          (1 * q_of_nat (nvec_total translation)) by ring.
        setoid_replace (q_of_nat (nvec_total translation) * q_of_nat multiplier)
          with (q_of_nat multiplier * q_of_nat (nvec_total translation)) by ring.
        apply Qmult_le_compat_r.
        + change (1 <= q_of_nat multiplier).
          unfold q_of_nat. change (inject_Z 1 <= inject_Z (Z.of_nat multiplier)).
          rewrite <- Zle_Qle. lia.
        + apply q_of_nat_nonnegative_directed.
      all: try (apply q_of_nat_nonzero; lia).
    }
    unfold approximant, coefficient, translated, qvec_scale.
    setoid_replace
      (point index -
        / q_of_nat (multiplier * replicas) *
          nvec_to_qvec (nvec_add translation
            (nvec_scale replicas period)) index)
      with (- (nvec_to_qvec translation index /
        q_of_nat (multiplier * replicas))).
    + rewrite Qabs_opp.
      rewrite Qabs_pos.
      * exact Hcoordinate_small.
      * apply Qmult_le_0_compat; [exact Hcoordinate_nonnegative|].
        apply Qlt_le_weak, Qinv_lt_0_compat. exact Hden_positive.
    + unfold nvec_to_qvec, nvec_add, nvec_scale in *.
      rewrite (StdVector.nth_map2 _ _ _ index index index eq_refl eq_refl).
      rewrite (StdVector.nth_map _ _ index index eq_refl).
      unfold q_of_nat in *.
      rewrite Nat2Z.inj_add, !Nat2Z.inj_mul, inject_Z_plus, !inject_Z_mult.
      assert (Hmultiplier_nonzero : ~ inject_Z (Z.of_nat multiplier) == 0).
      { intro Hzero.
        apply (Qlt_not_eq _ _
          (q_of_nat_positive_directed multiplier Hmultiplier)).
        unfold q_of_nat. symmetry. exact Hzero. }
      assert (Hreplicas_nonzero : ~ inject_Z (Z.of_nat replicas) == 0).
      { intro Hzero.
        apply (Qlt_not_eq _ _
          (q_of_nat_positive_directed replicas Hreplicas)).
        unfold q_of_nat. symmetry. exact Hzero. }
      assert (Hpoint : point index ==
          / inject_Z (Z.of_nat multiplier) *
            inject_Z (Z.of_nat (StdVector.nth period index))).
      { apply (proj1 (Qmult_inj_l _ _ (inject_Z (Z.of_nat multiplier))
          Hmultiplier_nonzero)).
        transitivity (inject_Z (Z.of_nat (StdVector.nth period index))).
        - exact Hcoordinate.
        - field. exact Hmultiplier_nonzero. }
      setoid_rewrite Hpoint.
      setoid_replace (/ inject_Z (Z.of_nat multiplier)) with
        (/ (inject_Z (Z.of_nat multiplier) * inject_Z (Z.of_nat replicas)) *
          inject_Z (Z.of_nat replicas)) by
        (apply qinv_product_cancel_right; assumption).
      unfold Qdiv, Qminus. ring.
Qed.

Lemma translated_period_closed_cone_inclusion : forall d
    (left right : NVec d -> Prop) translation,
    PeriodicNSet left ->
    (forall value, left value -> right (nvec_add translation value)) ->
    forall point,
      QClosure (Cone (NSetAsZ left)) point ->
      QClosure (Cone (NSetAsZ right)) point.
Proof.
  intros d left right translation Hperiodic Htranslate point Hclosure.
  apply qclosure_idempotent.
  eapply qclosure_monotone; [|exact Hclosure].
  intros value Hvalue.
  now apply translated_period_cone_closure with
    (left := left) (right := right) (translation := translation).
Qed.

Lemma directed_edge_difference_inclusion : forall d
    (system : IBVAS d) (source target : DirectedIRun system),
    DirectedIRunEdge source target ->
    DirectedConeIncluded source target ->
    forall difference,
      Difference (DirectedPeriod source) difference ->
      Difference (DirectedPeriod target) difference.
Proof.
  intros d system source target Hedge Hcones difference Hdifference.
  destruct (directed_edge_translated_offset_inclusion d system source target
    Hedge Hcones) as [translation [_ Htranslate]].
  exact (translated_difference_inclusion d (DirectedOffset source)
    (DirectedOffset target) translation Htranslate difference Hdifference).
Qed.

Lemma directed_edge_closed_cone_inclusion : forall d
    (system : IBVAS d) (source target : DirectedIRun system),
    DirectedIRunEdge source target ->
    DirectedConeIncluded source target ->
    forall point,
      QClosure (Cone (DirectedPeriod source)) point ->
      QClosure (Cone (DirectedPeriod target)) point.
Proof.
  intros d system source target Hedge Hcones point Hclosure.
  destruct (directed_edge_translated_offset_inclusion d system source target
    Hedge Hcones) as [translation [_ Htranslate]].
  exact (translated_period_closed_cone_inclusion d
    (DirectedOffset source) (DirectedOffset target) translation
    (directed_offset_periodic d system source) Htranslate point Hclosure).
Qed.

Theorem lemma_3_13_directed_closed_period_inclusion : forall d
    (system : IBVAS d) (source target : DirectedIRun system),
    DirectedIRunEdge source target ->
    DirectedConeIncluded source target ->
    forall value,
      DirectedClosedPeriod source value ->
      DirectedClosedPeriod target value.
Proof.
  intros d system source target Hedge Hcones value
    [Hdifference Hclosure]. split.
  - eapply directed_edge_difference_inclusion; eauto.
  - eapply directed_edge_closed_cone_inclusion; eauto.
Qed.

Corollary mutually_reachable_equal_cones_closed_period_equal : forall d
    (system : IBVAS d) (left right : DirectedIRun system),
    DirectedIRunEdge left right ->
    DirectedIRunEdge right left ->
    (forall point, DirectedCone left point <-> DirectedCone right point) ->
    forall value,
      DirectedClosedPeriod left value <-> DirectedClosedPeriod right value.
Proof.
  intros d system left right Hlr Hrl Hcones value. split.
  - apply lemma_3_13_directed_closed_period_inclusion; [exact Hlr|].
    intros point Hpoint. now apply (proj1 (Hcones point)).
  - apply lemma_3_13_directed_closed_period_inclusion; [exact Hrl|].
    intros point Hpoint. now apply (proj2 (Hcones point)).
Qed.
