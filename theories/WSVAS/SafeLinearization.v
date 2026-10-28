From Coq Require Import Classical_Prop Lia Vector ZArith.
From KruskalAfProp Require Import af.af af.af_tools af.af_ramsey.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization ClosedLinearizationL2
  CenterPushIn Periodic QConeCore RationalSpan.
From Mell.Geometry Require Import RationalClosure.
From Mell.Order Require Import AlmostFullBridge PeriodicOrder.
From Mell.Semilinear Require Import Presentation LinearEquations Closure.
From Mell.VAS Require Import AlmostSemilinearProjection Intraproductions
  PeriodicIntersection Runs.
From Mell.BVAS Require Import RunOrder.
From Mell.WSVAS Require Import System Runs Amalgamation RunOrder
  SemilinearRayOrder.

Definition ClosedLinearizationN {d} (set : NVec d -> Prop) : NVec d -> Prop :=
  fun value => ClosedLinearization (NSetAsZ set) (nvec_to_zvec value).

Definition NSetTranslate {d} (base : NVec d) (set : NVec d -> Prop) : NVec d -> Prop :=
  fun value => exists offset, set offset /\ value = nvec_add base offset.

Definition ReachWSVASFromSet {d} (system : WSVAS d)
    (sources targets : NVec d -> Prop) : Prop :=
  forall run : WSRun system,
    ValidWSRun run -> sources (ws_source run) -> targets (ws_target run).

Lemma nset_as_z_nonnegative : forall d (set : NVec d -> Prop),
  NonnegativeSet (NSetAsZ set).
Proof.
  intros d set value [natural [-> _]] index.
  unfold nvec_to_zvec.
  rewrite (Vector.nth_map _ _ index index eq_refl). lia.
Qed.
Lemma periodic_nset_nsmul : forall d (set : NVec d -> Prop),
  PeriodicNSet set -> forall coefficient value,
  set value -> set (nvec_scale coefficient value).
Proof.
  intros d set [Hzero Hadd] coefficient value Hvalue.
  induction coefficient as [|coefficient IH].
  - rewrite nvec_scale_zero. exact Hzero.
  - rewrite nvec_scale_succ. now apply Hadd.
Qed.

Lemma periodic_nset_in_closed_linearization : forall d
    (set : NVec d -> Prop),
  PeriodicNSet set -> forall value,
  set value -> ClosedLinearizationN set value.
Proof.
  intros d set Hperiodic value Hvalue. split.
  - apply periodic_member_in_difference with
      (set := NSetAsZ set) (value := nvec_to_zvec value).
    + now apply periodic_nset_as_z.
    + exists value. auto.
  - apply qclosure_extensive, cone_contains_source.
    exists value. auto.
Qed.

Lemma safe_asymptotic_as_z : forall d (set : NVec d -> Prop),
  AsymptoticallyDefinableNSet set -> AsymptoticallyDefinable (NSetAsZ set).
Proof. intros d set [_ Hcone]. exact Hcone. Qed.

Lemma safe_closed_periodic : forall d (set : NVec d -> Prop),
  PeriodicNSet set -> PeriodicNSet (ClosedLinearizationN set).
Proof.
  intros d set Hset. pose proof (closed_linearization_periodic d
    (NSetAsZ set) (periodic_nset_as_z d set Hset)) as Hperiodic.
  split.
  - unfold ClosedLinearizationN. rewrite nvec_zero_to_zvec.
    exact (proj1 Hperiodic).
  - intros left right Hleft Hright. unfold ClosedLinearizationN in *.
    rewrite nvec_to_zvec_add. now apply (proj2 Hperiodic).
Qed.

Lemma safe_closed_wqo : forall d (set : NVec d -> Prop),
  PeriodicNSet set -> AsymptoticallyDefinableNSet set ->
  @afs (NVec d) (ClosedLinearizationN set)
    (fun left right => nvec_le left right /\
      PeriodicLe (ClosedLinearization (NSetAsZ set))
        (nvec_to_zvec left) (nvec_to_zvec right)).
Proof.
  intros d set Hperiodic Hasymptotic.
  pose proof (closed_linearization_finitely_generated d (NSetAsZ set)
    (periodic_nset_as_z d set Hperiodic) (nset_as_z_nonnegative d set)
    (safe_asymptotic_as_z d set Hasymptotic)) as Hfinite.
  pose proof (finitely_generated_periodic_wqo d
    (ClosedLinearization (NSetAsZ set)) Hfinite) as Hwqo.
  assert (Htransport : @afs (NVec d) (ClosedLinearizationN set)
      (fun left right => PeriodicLe (ClosedLinearization (NSetAsZ set))
        (nvec_to_zvec left) (nvec_to_zvec right))).
  { eapply afs_rel_morph with
      (f := fun integer natural => integer = nvec_to_zvec natural)
      (P := ClosedLinearization (NSetAsZ set))
      (R := PeriodicLe (ClosedLinearization (NSetAsZ set))).
    - intros natural Hnatural. exists (nvec_to_zvec natural). auto.
    - intros left right left' right' _ _ _ _ -> -> Hle. exact Hle.
    - exact Hwqo. }
  assert (Hcoordinate : @afs (NVec d) (ClosedLinearizationN set) nvec_le).
  { apply af_sub_rel_afs, af_af_sub_rel, nvec_le_almost_full. }
  apply af_sub_rel_afs.
  exact (af_inter (afs_af_sub_rel Hcoordinate) (afs_af_sub_rel Htransport)).
Qed.
Lemma safe_push_in_n : forall d (set : NVec d -> Prop),
  PeriodicNSet set ->
  exists anchor, set anchor /\
    forall offset point,
      ClosedLinearizationN set offset ->
      NSetTranslate anchor (ClosedLinearizationN set) point ->
      exists coefficient, (1 <= coefficient)%nat /\
        set (nvec_add offset (nvec_scale coefficient point)).
Proof.
  intros d set Hperiodic.
  destruct (closed_linearization_push_in d (NSetAsZ set)
    (periodic_nset_as_z d set Hperiodic) (nset_as_z_nonnegative d set))
    as [anchorZ [[anchor [HanchorZ Hanchor]] Hpush]]. subst anchorZ.
  exists anchor. split; [exact Hanchor|].
  intros offset point Hoffset [point_offset [Hpoint_offset ->]].
  assert (Hsub : zvec_sub (nvec_to_zvec (nvec_add anchor point_offset))
      (nvec_to_zvec anchor) = nvec_to_zvec point_offset).
  { rewrite nvec_to_zvec_add. apply zvec_ext. intro index.
    unfold zvec_sub, zvec_add.
    repeat rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl).
    lia. }
  destruct Hoffset as [Hoffset_difference _].
  destruct (Hpush (nvec_to_zvec offset)
      (nvec_to_zvec (nvec_add anchor point_offset)) Hoffset_difference)
    as [radius Hradius].
  - rewrite Hsub. exact Hpoint_offset.
  - exists (S radius). split; [lia|]. specialize (Hradius 1%nat).
    replace (radius + 1)%nat with (S radius) in Hradius by lia.
    destruct Hradius as [natural [HnaturalZ Hnatural]].
    replace (nvec_add offset
      (nvec_scale (S radius) (nvec_add anchor point_offset))) with natural.
    + exact Hnatural.
    + apply nvec_to_zvec_injective. rewrite nvec_to_zvec_add,
        nvec_scale_to_zvec. symmetry. exact HnaturalZ.
Qed.

Section SafeLinearization.
Context {d : nat} (system : WSVAS d).

Definition SafePayload (period target : NVec d -> Prop) : Type :=
  ({ run : WSRun system | ValidWSRun run } *
   ({ offset : NVec d | ClosedLinearizationN period offset } *
    { value : NVec d | ~ target value }))%type.

Definition SafePayloadLe (period target : NVec d -> Prop)
    (left right : SafePayload period target) : Prop :=
  WSRunOrder system (proj1_sig (fst left)) (proj1_sig (fst right)) /\
  (nvec_le (proj1_sig (fst (snd left))) (proj1_sig (fst (snd right))) /\
   PeriodicLe (ClosedLinearization (NSetAsZ period))
     (nvec_to_zvec (proj1_sig (fst (snd left))))
     (nvec_to_zvec (proj1_sig (fst (snd right))))) /\
  RayLe (fun value => ~ target value)
    (proj1_sig (snd (snd left))) (proj1_sig (snd (snd right))).

Lemma safe_payload_almost_full : forall period target,
  PeriodicNSet period -> AsymptoticallyDefinableNSet period ->
  Semilinear target -> af (SafePayloadLe period target).
Proof.
  intros period target Hperiodic Hasymptotic Htarget.
  unfold SafePayloadLe, SafePayload.
  pose proof (@afs_af_sub_rel _ _ _ (corollary_c_2_wsrun_wqo system)) as Hrun.
  pose proof (@afs_af_sub_rel _ _ _
    (safe_closed_wqo d period Hperiodic Hasymptotic)) as Hperiod.
  pose proof (@afs_af_sub_rel _ _ _
    (semilinear_complement_ray_almost_full d target Htarget)) as Hray.
  eapply af_mono; [|exact (af_product Hrun (af_product Hperiod Hray))].
  intros [left_run [left_q left_target]]
    [right_run [right_q right_target]]. cbn. tauto.
Qed.

Definition SafeCounterexample (base anchor : NVec d)
    (period target : NVec d -> Prop) (index : nat)
    (payload : SafePayload period target) : Prop :=
  ws_source (proj1_sig (fst payload)) =
    nvec_add (nvec_add base (nvec_scale index anchor))
      (proj1_sig (fst (snd payload))) /\
  ws_target (proj1_sig (fst payload)) = proj1_sig (snd (snd payload)).

Theorem lemma_5_4_wsvas_safe_linearization :
  forall (base : NVec d) (period target : NVec d -> Prop),
  PeriodicNSet period ->
  AsymptoticallyDefinableNSet period ->
  Semilinear target ->
  ReachWSVASFromSet system (NSetTranslate base period) target ->
  exists offset,
    period offset /\
    ReachWSVASFromSet system
      (NSetTranslate (nvec_add base offset)
        (ClosedLinearizationN period)) target.
Proof.
  intros base period target Hperiodic Hasymptotic Htarget Hreach.
  destruct (safe_push_in_n d period Hperiodic)
    as [anchor [Hanchor Hpush]].
  apply NNPP. intro Hnone.
  assert (Htotal : forall index,
      exists payload : SafePayload period target,
        SafeCounterexample base anchor period target index payload).
  { intro index.
    assert (Hindex : period (nvec_scale index anchor)).
    { now apply periodic_nset_nsmul. }
    assert (Hnotreach : ~ ReachWSVASFromSet system
        (NSetTranslate (nvec_add base (nvec_scale index anchor))
          (ClosedLinearizationN period)) target).
    { intro Hlayer. apply Hnone. exists (nvec_scale index anchor).
      split; assumption. }
    destruct (classic (exists run : WSRun system,
        ValidWSRun run /\
        NSetTranslate (nvec_add base (nvec_scale index anchor))
          (ClosedLinearizationN period) (ws_source run) /\
        ~ target (ws_target run))) as
      [[run [Hvalid [[q [Hq Hsource]] Hbad]]]|Hmissing].
    - exists (exist _ run Hvalid,
        (exist _ q Hq, exist _ (ws_target run) Hbad)).
      split; [now symmetry|reflexivity].
    - exfalso. apply Hnotreach. intros run Hvalid Hsource.
      destruct (classic (target (ws_target run))) as [Hgood|Hbad];
        [exact Hgood|].
      exfalso. apply Hmissing. now exists run. }
  pose proof (safe_payload_almost_full period target Hperiodic
    Hasymptotic Htarget) as Haf.
  destruct ((af_af_rec_total Haf) (SafeCounterexample base anchor period target)
    Htotal) as [bound [i [j [left [right
      [[Hij Hjb] [Hleft [Hright Hle]]]]]]]].
  clear bound Hjb.
  destruct left as [[left_run Hleft_valid]
    [[left_q Hleft_q] [left_target Hleft_bad]]].
  destruct right as [[right_run Hright_valid]
    [[right_q Hright_q] [right_target Hright_bad]]].
  cbn in Hleft, Hright, Hle.
  destruct Hleft as [Hleft_source Hleft_target].
  destruct Hright as [Hright_source Hright_target].
  destruct Hle as [Hrun_order [[Hq_le Hq_period] Hray]].
  change (ws_source left_run =
    nvec_add (nvec_add base (nvec_scale i anchor)) left_q) in Hleft_source.
  change (ws_target left_run = left_target) in Hleft_target.
  change (ws_source right_run =
    nvec_add (nvec_add base (nvec_scale j anchor)) right_q) in Hright_source.
  change (ws_target right_run = right_target) in Hright_target.
  change (WSRunOrder system left_run right_run) in Hrun_order.
  change (nvec_le left_q right_q) in Hq_le.
  change (PeriodicLe (ClosedLinearization (NSetAsZ period))
    (nvec_to_zvec left_q) (nvec_to_zvec right_q)) in Hq_period.
  change (RayLe (fun value => ~ target value)
    left_target right_target) in Hray.
  destruct Hray as [target_step [Hright_target_step Hray_bad]].
  set (q_step := nvec_sub_local right_q left_q).
  assert (Hright_q_exact : right_q = nvec_add left_q q_step).
  { unfold q_step. apply nvec_sub_exact_local. exact Hq_le. }
  assert (Hq_step : ClosedLinearizationN period q_step).
  { unfold ClosedLinearizationN. unfold PeriodicLe in Hq_period.
    rewrite Hright_q_exact, nvec_to_zvec_add in Hq_period.
    replace (zvec_sub
      (zvec_add (nvec_to_zvec left_q) (nvec_to_zvec q_step))
      (nvec_to_zvec left_q)) with (nvec_to_zvec q_step) in Hq_period.
    - exact Hq_period.
    - apply zvec_ext. intro coordinate. unfold zvec_sub, zvec_add.
      repeat rewrite (Vector.nth_map2 _ _ _ coordinate coordinate coordinate
        eq_refl eq_refl). lia. }
  set (y := nvec_add (nvec_scale i anchor) left_q).
  set (tail_factor := (j - i - 1)%nat).
  set (x_tail := nvec_add (nvec_scale tail_factor anchor) q_step).
  set (x := nvec_add anchor x_tail).
  assert (Hanchor_closed : ClosedLinearizationN period anchor).
  { now apply periodic_nset_in_closed_linearization. }
  assert (Hy : ClosedLinearizationN period y).
  { unfold y. apply (proj2 (safe_closed_periodic d period Hperiodic)).
    - apply periodic_nset_in_closed_linearization with (set := period);
        [exact Hperiodic|].
      now apply periodic_nset_nsmul.
    - exact Hleft_q. }
  assert (Hxtail : ClosedLinearizationN period x_tail).
  { unfold x_tail. apply (proj2 (safe_closed_periodic d period Hperiodic)).
    - apply periodic_nset_in_closed_linearization with (set := period);
        [exact Hperiodic|].
      now apply periodic_nset_nsmul.
    - exact Hq_step. }
  assert (Hx : NSetTranslate anchor (ClosedLinearizationN period) x).
  { exists x_tail. split; [exact Hxtail|reflexivity]. }
  destruct (Hpush y x Hy Hx) as [factor [Hfactor Hperiod_offset]].
  assert (Hsource_step : ws_source right_run =
      nvec_add (ws_source left_run) x).
  { rewrite Hleft_source, Hright_source. unfold x, x_tail, tail_factor, y.
    rewrite Hright_q_exact.
    apply (proj1 (Vector.eq_nth_iff nat d _ _)).
    intros coordinate coordinate' Heq; subst coordinate'.
    unfold nvec_add, nvec_scale, q_step, nvec_sub_local.
    repeat rewrite (Vector.nth_map2 _ _ _ coordinate coordinate coordinate
      eq_refl eq_refl).
    repeat rewrite (Vector.nth_map _ _ coordinate coordinate eq_refl).
    specialize (Hq_le coordinate). nia. }
  destruct (corollary_5_3_wsvas_run_scaling system left_run right_run factor
    Hleft_valid Hright_valid Hrun_order Hfactor) as
    [scaled [Hscaled_valid [Hright_scaled [Hscaled_source Hscaled_target]]]].
  assert (Hscaled_source_exact : ws_source scaled =
      nvec_add base (nvec_add y (nvec_scale factor x))).
  { apply (proj1 (Vector.eq_nth_iff nat d _ _)).
    intros coordinate coordinate' Heq; subst coordinate'.
    pose proof (f_equal (fun value : NVec d => Vector.nth value coordinate)
      Hscaled_source) as Hscale.
    pose proof (f_equal (fun value : NVec d => Vector.nth value coordinate)
      Hsource_step) as Hstep.
    pose proof (f_equal (fun value : NVec d => Vector.nth value coordinate)
      Hleft_source) as Hbase.
    unfold y.
    unfold nvec_add, nvec_scale in *.
    repeat rewrite (Vector.nth_map2 _ _ _ coordinate coordinate coordinate
      eq_refl eq_refl) in *.
    repeat rewrite (Vector.nth_map _ _ coordinate coordinate eq_refl) in *.
    nia. }
  assert (Hscaled_target_exact : ws_target scaled =
      nvec_add (ws_target left_run) (nvec_scale factor target_step)).
  { rewrite Hleft_target. rewrite Hleft_target, Hright_target in Hscaled_target.
    apply (proj1 (Vector.eq_nth_iff nat d _ _)).
    intros coordinate coordinate' Heq; subst coordinate'.
    pose proof (f_equal (fun value : NVec d => Vector.nth value coordinate)
      Hscaled_target) as Hscale.
    pose proof (f_equal (fun value : NVec d => Vector.nth value coordinate)
      Hright_target_step) as Hstep.
    unfold nvec_add, nvec_scale in *.
    repeat rewrite (Vector.nth_map2 _ _ _ coordinate coordinate coordinate
      eq_refl eq_refl) in *.
    repeat rewrite (Vector.nth_map _ _ coordinate coordinate eq_refl) in *.
    nia. }
  specialize (Hray_bad factor).
  apply Hray_bad. rewrite <- Hleft_target, <- Hscaled_target_exact.
  apply Hreach with (run := scaled); [exact Hscaled_valid|].
  exists (nvec_add y (nvec_scale factor x)). split;
    [exact Hperiod_offset|exact Hscaled_source_exact].
Qed.

End SafeLinearization.

Lemma closed_linearization_push_in_n : forall d (set : NVec d -> Prop),
  PeriodicNSet set ->
  exists anchor, set anchor /\
    forall offset point,
      ClosedLinearizationN set offset ->
      NSetTranslate anchor (ClosedLinearizationN set) point ->
      exists coefficient,
        (1 <= coefficient)%nat /\
        set (nvec_add offset (nvec_scale coefficient point)).
Proof.
  intros d set Hperiodic.
  destruct (closed_linearization_push_in d (NSetAsZ set)
    (periodic_nset_as_z d set Hperiodic)
    (nset_as_z_nonnegative d set)) as [anchorZ [Hanchor Hpush]].
  destruct Hanchor as [anchor [HanchorZ Hanchor]]. subst anchorZ.
  exists anchor. split; [exact Hanchor|].
  intros offset point Hoffset [point_offset [Hpoint_offset Hpoint]].
  subst point.
  assert (Hsub : zvec_sub
      (nvec_to_zvec (nvec_add anchor point_offset))
      (nvec_to_zvec anchor) = nvec_to_zvec point_offset).
  { rewrite nvec_to_zvec_add. apply zvec_ext. intro index.
    unfold zvec_sub, zvec_add.
    repeat rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl).
    lia. }
  destruct Hoffset as [Hoffset_difference Hoffset_closure].
  destruct (Hpush (nvec_to_zvec offset)
      (nvec_to_zvec (nvec_add anchor point_offset))
      Hoffset_difference) as [radius Hradius].
  - rewrite Hsub. exact Hpoint_offset.
  - set (coefficient := S radius).
    exists coefficient. split; [unfold coefficient; lia|].
    specialize (Hradius 1%nat).
    replace (radius + 1)%nat with coefficient in Hradius by
      (unfold coefficient; lia).
    destruct Hradius as [natural [HnaturalZ Hnatural]].
    assert (Heq : natural = nvec_add offset
        (nvec_scale coefficient (nvec_add anchor point_offset))).
    { apply nvec_to_zvec_injective. symmetry.
      rewrite nvec_to_zvec_add, nvec_scale_to_zvec.
      exact HnaturalZ. }
    now rewrite <- Heq.
Qed.

Lemma asymptotically_definable_nset_as_z : forall d (set : NVec d -> Prop),
  AsymptoticallyDefinableNSet set ->
  AsymptoticallyDefinable (NSetAsZ set).
Proof. intros d set [_ Hcone]. exact Hcone. Qed.

Lemma closed_linearization_n_periodic : forall d (set : NVec d -> Prop),
  PeriodicNSet set -> PeriodicNSet (ClosedLinearizationN set).
Proof.
  intros d set Hset. pose proof (closed_linearization_periodic d
    (NSetAsZ set) (periodic_nset_as_z d set Hset)) as Hperiodic.
  split.
  - unfold ClosedLinearizationN.
    replace (nvec_to_zvec (nvec_zero d)) with (zvec_zero d).
    + exact (proj1 Hperiodic).
    + apply zvec_ext. intro index. unfold nvec_to_zvec, nvec_zero, zvec_zero.
      rewrite (Vector.nth_map _ _ index index eq_refl),
        (Vector.const_nth nat 0%nat d index),
        (Vector.const_nth Z 0%Z d index).
      reflexivity.
  - intros left right Hleft Hright. unfold ClosedLinearizationN in *.
    rewrite nvec_to_zvec_add. now apply (proj2 Hperiodic).
Qed.

Lemma closed_linearization_n_wqo : forall d (set : NVec d -> Prop),
  PeriodicNSet set -> AsymptoticallyDefinableNSet set ->
  @afs (NVec d) (ClosedLinearizationN set)
    (fun left right =>
      nvec_le left right /\
      PeriodicLe (ClosedLinearization (NSetAsZ set))
        (nvec_to_zvec left) (nvec_to_zvec right)).
Proof.
  intros d set Hperiodic Hasymptotic.
  pose proof (closed_linearization_finitely_generated d (NSetAsZ set)
    (periodic_nset_as_z d set Hperiodic)
    (nset_as_z_nonnegative d set)
    (asymptotically_definable_nset_as_z d set Hasymptotic)) as Hfinite.
  pose proof (finitely_generated_periodic_wqo d
    (ClosedLinearization (NSetAsZ set)) Hfinite) as Hwqo.
  assert (Htransport : @afs (NVec d) (ClosedLinearizationN set)
      (fun left right => PeriodicLe (ClosedLinearization (NSetAsZ set))
        (nvec_to_zvec left) (nvec_to_zvec right))).
  { eapply afs_rel_morph with
    (f := fun integer natural => integer = nvec_to_zvec natural)
    (P := ClosedLinearization (NSetAsZ set))
    (R := PeriodicLe (ClosedLinearization (NSetAsZ set))).
  - intros natural Hnatural. exists (nvec_to_zvec natural). split;
      [exact Hnatural|reflexivity].
  - intros left right left' right' Hleft Hright Hleft' Hright'
      -> -> Hle. exact Hle.
  - exact Hwqo. }
  assert (Hcoordinate : @afs (NVec d) (ClosedLinearizationN set) nvec_le).
  { apply af_sub_rel_afs, af_af_sub_rel, nvec_le_almost_full. }
  apply af_sub_rel_afs.
  exact (af_inter (afs_af_sub_rel Hcoordinate) (afs_af_sub_rel Htransport)).
Qed.
