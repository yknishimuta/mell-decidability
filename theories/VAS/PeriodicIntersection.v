From Coq Require Import Lia List QArith Qring Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Presentation LinearEquations.
From Mell.BVAS Require Import RunOrder.
From Mell.Geometry Require Import MathCompBridge Periodic Cone QConeCore
  RationalDefinability ClosedLinearization LatticeGordanV
  LatticeGordanInterface Faces QIntegerHRep RationalHToV
  FaceStrippingLemma610.
From Mell.Order Require Import PeriodicOrder.
From Mell.VAS Require Import Transformer RelationCone AsymptoticRelation
  LinearReachRelation.

Import ListNotations.
Open Scope Q_scope.

Lemma fin_to_nat_FS_value_pi : forall n (index : Fin.t n),
    proj1_sig (Fin.to_nat (Fin.FS index)) =
      S (proj1_sig (Fin.to_nat index)).
Proof.
  intros n index. induction index; cbn; [reflexivity|].
  destruct (Fin.to_nat index). reflexivity.
Qed.

Lemma periodic_intersection : forall d (P Q : ZSet d),
    Periodic P -> Periodic Q ->
    Periodic (fun value => P value /\ Q value).
Proof.
  intros d P Q [HPzero HPadd] [HQzero HQadd]. split.
  - now split.
  - intros left right [HPl HPq] [HQl HQq]. split;
      [now apply HPadd|now apply HQadd].
Qed.

Fixpoint qinner_term_from {d} (position : nat) (normal : Vector.t Z d) : QTerm :=
  match normal with
  | @Vector.nil _ => QTConst 0
  | @Vector.cons _ head tail_d tail =>
      QTAdd (QTScale (inject_Z head) (QTVar position))
        (qinner_term_from (S position) tail)
  end.

Lemma qinner_term_from_closed : forall d position (normal : Vector.t Z d) bound,
    (position + d <= bound)%nat ->
    qterm_closed bound (qinner_term_from position normal) = true.
Proof.
  intros d position normal. revert position.
  induction normal as [|head d tail IH];
    intros position bound Hbound; cbn.
  - reflexivity.
  - apply andb_true_iff. split.
    + apply Nat.ltb_lt. lia.
    + apply IH. lia.
Qed.

Lemma qinner_term_from_correct : forall d position (normal : Vector.t Z d)
    (value : QVec d) environment,
    (forall index, environment
      (position + proj1_sig (Fin.to_nat index))%nat == value index) ->
    qterm_semantics environment (qinner_term_from position normal) ==
      qdot (Vector.map inject_Z normal) (qvec_to_vector d value).
Proof.
  intros d position normal. revert position.
  induction normal as [|head d tail IH];
    intros position value environment Hagree; cbn.
  - reflexivity.
  - apply Qplus_comp.
    + apply Qmult_comp; [reflexivity|].
      pose proof (Hagree Fin.F1) as Hhead. cbn in Hhead.
      now rewrite Nat.add_0_r in Hhead.
    + apply (IH (S position) (fun index => value (Fin.FS index)) environment).
      intro index.
      pose proof (Hagree (Fin.FS index)) as Htail.
      rewrite fin_to_nat_FS_value_pi in Htail.
      replace (S position + proj1_sig (Fin.to_nat index))%nat with
        (position + S (proj1_sig (Fin.to_nat index)))%nat by lia.
      exact Htail.
Qed.

Definition qnormal_constraint {d} (normal : ZVec d) : QFormula :=
  QFLe (QTConst 0) (qinner_term_from 0 normal).

Fixpoint qformula_and_list_pi (formulas : list QFormula) : QFormula :=
  match formulas with
  | [] => QFTop
  | formula :: tail => QFAnd formula (qformula_and_list_pi tail)
  end.

Lemma qformula_and_list_pi_closed : forall formulas bound,
    List.Forall (fun formula => qformula_closed bound formula = true) formulas ->
    qformula_closed bound (qformula_and_list_pi formulas) = true.
Proof.
  intros formulas bound H. induction H; cbn; [reflexivity|].
  now rewrite H, IHForall.
Qed.

Lemma qformula_and_list_pi_correct : forall formulas environment,
    qformula_semantics environment (qformula_and_list_pi formulas) <->
    forall formula, List.In formula formulas -> qformula_semantics environment formula.
Proof.
  intros formulas. induction formulas as [|head tail IH]; intro environment; cbn.
  - tauto.
  - rewrite IH. split.
    + intros [Hhead Htail] formula [<-|Hin]; auto.
    + intro H. split; [apply H; now left|]. intros; apply H; now right.
Qed.

Lemma qnormal_constraint_correct : forall d (normal : ZVec d) value,
    qformula_semantics (qvec_environment value) (qnormal_constraint normal) <->
    0 <= qinner (zvec_to_qvec normal) value.
Proof.
  intros d normal value. unfold qnormal_constraint. cbn.
  assert (Heq : qterm_semantics (qvec_environment value)
      (qinner_term_from 0 normal) ==
      qdot (Vector.map inject_Z normal) (qvec_to_vector d value)).
  { apply qinner_term_from_correct. intro index. cbn.
    rewrite qvec_environment_inside. reflexivity. }
  unfold qinner, qrow_apply.
  assert (Hdot : qdot (Vector.map inject_Z normal) (qvec_to_vector d value) ==
      qdot (qvec_to_vector d (zvec_to_qvec normal)) (qvec_to_vector d value)).
  { apply qdot_ext; [|intro index; reflexivity]. intro index.
    rewrite (Vector.nth_map _ _ index index eq_refl), qvec_to_vector_nth.
    reflexivity. }
  setoid_rewrite Heq. setoid_rewrite Hdot. reflexivity.
Qed.

Lemma qdefinable_integer_hrep : forall d (normals : list (ZVec d)),
    QDefinable (fun value : QVec d => forall normal,
      List.In normal normals -> 0 <= qinner (zvec_to_qvec normal) value).
Proof.
  intros d normals.
  exists (qformula_and_list_pi (List.map qnormal_constraint normals)). split.
  - apply qformula_and_list_pi_closed, List.Forall_forall.
    intros formula Hin. apply in_map_iff in Hin as [normal [<- Hin]].
    unfold qnormal_constraint. cbn. apply qinner_term_from_closed. lia.
  - intro value. rewrite qformula_and_list_pi_correct. split.
    + intros H formula Hin. apply in_map_iff in Hin as [normal [<- Hin]].
      apply (proj2 (qnormal_constraint_correct d normal value)). now apply H.
    + intros H normal Hin.
      apply (proj1 (qnormal_constraint_correct d normal value)).
      apply H. apply in_map. exact Hin.
Qed.

Theorem rational_polyhedral_cone_qdefinable : forall d (cone : QSet d),
    RationalPolyhedralCone cone -> QDefinable cone.
Proof.
  intros d cone Hpolyhedral.
  destruct (polyhedral_cone_integer_hrep d cone Hpolyhedral)
    as [normals Hnormals].
  eapply qdefinable_congr; [intro value; symmetry; apply Hnormals|].
  apply qdefinable_integer_hrep.
Qed.

Lemma cone_subset : forall d (P Q : ZSet d),
    (forall value, P value -> Q value) ->
    forall point, Cone P point -> Cone Q point.
Proof.
  intros d P Q Hsubset point [generated [Hgenerated Hpoint]].
  assert (Hlift : forall generated, ConeGen P generated -> ConeGen Q generated).
  { intros value Hvalue. induction Hvalue.
    - constructor.
    - apply cone_add; [exact H|now apply Hsubset|exact IHHvalue]. }
  exists generated. split; [now apply Hlift|exact Hpoint].
Qed.

Theorem periodic_cone_intersection : forall d (P Q : ZSet d)
    (point : QVec d),
    Periodic P -> Periodic Q ->
    (Cone (fun value => P value /\ Q value) point <->
     Cone P point /\ Cone Q point).
Proof.
  intros d P Q point HP HQ. split.
  - intro H. split.
    + eapply cone_subset with (P := fun value => P value /\ Q value).
      * intros value Hboth. exact (proj1 Hboth).
      * exact H.
    + eapply cone_subset with (P := fun value => P value /\ Q value).
      * intros value Hboth. exact (proj2 Hboth).
      * exact H.
  - intros [HPcone HQcone].
    apply (proj1 (periodic_cone_positive_multiple_iff d P point HP)) in HPcone.
    apply (proj1 (periodic_cone_positive_multiple_iff d Q point HQ)) in HQcone.
    destruct HPcone as [n [p [Hn [Hp Hpointp]]]].
    destruct HQcone as [m [q [Hm [Hq Hpointq]]]].
    assert (Heq : zvec_nsmul m p = zvec_nsmul n q).
    { apply zvec_to_qvec_injective. intro index.
      transitivity (qvec_scale (q_of_nat m) (zvec_to_qvec p) index).
      - apply zvec_nsmul_to_qvec_nat.
      - transitivity (q_of_nat m * (q_of_nat n * point index)).
        + unfold qvec_scale. apply Qmult_comp; [reflexivity|].
          symmetry. apply Hpointp.
        + transitivity (q_of_nat n * (q_of_nat m * point index)); [ring|].
          transitivity (qvec_scale (q_of_nat n) (zvec_to_qvec q) index).
          * unfold qvec_scale. apply Qmult_comp; [reflexivity|]. apply Hpointq.
          * symmetry. apply zvec_nsmul_to_qvec_nat. }
    apply (proj2 (periodic_cone_positive_multiple_iff d
      (fun value => P value /\ Q value) point
      (periodic_intersection d P Q HP HQ))).
    exists (n * m)%nat, (zvec_nsmul m p). split; [nia|]. split.
    + split.
      * now apply periodic_nsmul with (set := P).
      * rewrite Heq. now apply periodic_nsmul with (set := Q).
    + eapply qvec_eq_trans; [apply qvec_scale_nat_product|].
      intro index. unfold qvec_scale.
      transitivity (q_of_nat m * (q_of_nat n * point index)); [ring|].
      transitivity (q_of_nat m * zvec_to_qvec p index).
      * apply Qmult_comp; [reflexivity|apply Hpointp].
      * symmetry. apply zvec_nsmul_to_qvec_nat.
Qed.

Theorem lemma_6_2_qdefinable_intersection : forall d (P Q : ZSet d),
    Periodic P -> Periodic Q ->
    QDefinable (Cone P) -> QDefinable (Cone Q) ->
    QDefinable (Cone (fun value => P value /\ Q value)).
Proof.
  intros d P Q HP HQ HPdef HQdef.
  eapply qdefinable_congr.
  - intro point. symmetry. apply periodic_cone_intersection; assumption.
  - now apply qdefinable_intersection.
Qed.

Theorem lemma_6_2_asymptotically_definable_intersection : forall d
    (P Q : ZSet d),
    Periodic P -> Periodic Q ->
    AsymptoticallyDefinable P -> AsymptoticallyDefinable Q ->
    AsymptoticallyDefinable (fun value => P value /\ Q value).
Proof.
  intros d P Q HP HQ HPdef HQdef.
  now apply lemma_6_2_qdefinable_intersection.
Qed.

Lemma nrelation_as_z_intersection : forall d (R S : NRelation d) input output,
    NRelationAsZ (fun x y => R x y /\ S x y) input output <->
    NRelationAsZ R input output /\ NRelationAsZ S input output.
Proof.
  intros d R S input output. split.
  - intros [ni [no [Hin [Hout [HR HS]]]]]. split;
      exists ni, no; repeat split; assumption.
  - intros [[ri [ro [Hri [Hro HR]]]] [si [so [Hsi [Hso HS]]]]].
    assert (Ei : ri = si).
    { apply nvec_to_zvec_injective_relation. now rewrite <- Hri, <- Hsi. }
    assert (Eo : ro = so).
    { apply nvec_to_zvec_injective_relation. now rewrite <- Hro, <- Hso. }
    subst si; subst so. exists ri, ro. repeat split; assumption.
Qed.

Theorem asymptotically_definable_nrelation_intersection : forall d
    (R S : NRelation d),
    AsymptoticallyDefinableNRelation R ->
    AsymptoticallyDefinableNRelation S ->
    AsymptoticallyDefinableNRelation (fun input output => R input output /\ S input output).
Proof.
  intros d R S [[HRzero HRadd] HRdef] [[HSzero HSadd] HSdef]. split.
  - split; [now split|]. intros x1 y1 x2 y2 [HR1 HS1] [HR2 HS2].
    split; [now apply HRadd|now apply HSadd].
  - eapply qdefinable_congr.
    + intro pair. unfold RelationConePairs.
      rewrite <- periodic_cone_intersection with
        (P := ZRelationPairs (NRelationAsZ R))
        (Q := ZRelationPairs (NRelationAsZ S)).
      2: { apply periodic_zrelation_pairs_iff,
            periodic_nrelation_as_z. now split. }
      2: { apply periodic_zrelation_pairs_iff,
            periodic_nrelation_as_z. now split. }
      split; intro Hcone.
      * eapply cone_subset with
          (P := fun value => ZRelationPairs (NRelationAsZ R) value /\
            ZRelationPairs (NRelationAsZ S) value).
        -- intros integer_pair Hmember. unfold ZRelationPairs in *.
        now apply (proj2 (nrelation_as_z_intersection d R S
          (zpair_left integer_pair) (zpair_right integer_pair))).
        -- exact Hcone.
      * eapply cone_subset with
          (P := ZRelationPairs
            (NRelationAsZ (fun input output => R input output /\ S input output))).
        -- intros integer_pair Hmember. unfold ZRelationPairs in *.
        now apply (proj1 (nrelation_as_z_intersection d R S
          (zpair_left integer_pair) (zpair_right integer_pair))).
        -- exact Hcone.
    + now apply qdefinable_intersection.
Qed.

Definition generated_period_zgenerators {d}
    (generators : list (NVec d * NVec d)) : list (ZVec (d + d)) :=
  List.map (fun generator =>
    zpair_pack (nvec_to_zvec (fst generator))
      (nvec_to_zvec (snd generator))) generators.

Lemma nvec_zero_to_zvec : forall d,
    nvec_to_zvec (nvec_zero d) = zvec_zero d.
Proof.
  intro d. apply zvec_ext. intro index. unfold nvec_to_zvec, nvec_zero,
    zvec_zero. rewrite (Vector.nth_map _ _ index index eq_refl),
      !Vector.const_nth. reflexivity.
Qed.

Lemma nvec_scale_to_zvec : forall d coefficient (value : NVec d),
    nvec_to_zvec (nvec_scale coefficient value) =
      zvec_nsmul coefficient (nvec_to_zvec value).
Proof.
  intros d coefficient value. apply zvec_ext. intro index.
  unfold nvec_to_zvec, nvec_scale.
  rewrite (Vector.nth_map _ _ index index eq_refl),
    (Vector.nth_map _ _ index index eq_refl), nth_zvec_nsmul,
    (Vector.nth_map _ _ index index eq_refl).
  apply Nat2Z.inj_mul.
Qed.

Lemma generated_period_linear_combination : forall d
    (generators : list (NVec d * NVec d))
    (coefficients : NVec (List.length generators)),
    zvec_linear_combination (generated_period_zgenerators generators)
      (Vector.to_list coefficients) =
    zpair_pack (nvec_to_zvec (GeneratedInput generators coefficients))
      (nvec_to_zvec (GeneratedOutput generators coefficients)).
Proof.
  intros d generators. induction generators as [|[input output] tail IH];
    intro coefficients.
  - refine (Vector.case0 (fun coefficients => _) _ coefficients). cbn.
    rewrite !nvec_zero_to_zvec. symmetry. apply zpair_pack_zero.
  - refine (Vector.caseS' coefficients (fun coefficients => _) _).
    intros coefficient coefficients'.
    unfold generated_period_zgenerators in IH |- *. cbn.
    change (zvec_add
      (zvec_nsmul coefficient
        (zpair_pack (nvec_to_zvec input) (nvec_to_zvec output)))
      (zvec_linear_combination
        (List.map (fun generator : NVec d * NVec d =>
          zpair_pack (nvec_to_zvec (fst generator))
            (nvec_to_zvec (snd generator))) tail)
        (Vector.to_list coefficients')) =
      zpair_pack
        (nvec_to_zvec (nvec_add (nvec_scale coefficient input)
          (GeneratedInput tail coefficients')))
        (nvec_to_zvec (nvec_add (nvec_scale coefficient output)
          (GeneratedOutput tail coefficients')))).
    rewrite IH, zpair_pack_nsmul, zpair_pack_add,
      <- nvec_scale_to_zvec, <- nvec_scale_to_zvec,
      <- nvec_to_zvec_add, <- nvec_to_zvec_add. reflexivity.
Qed.

Lemma generated_period_pair_generator : forall d
    (generators : list (NVec d * NVec d)) input output,
    List.In (input, output) generators ->
    GeneratedPeriodPair generators input output.
Proof.
  intros d generators. induction generators as [|[head_input head_output] tail IH];
    intros input output Hin; [contradiction|].
  destruct Hin as [Heq|Hin].
  - inversion Heq; subst. exists (@Vector.cons nat 1%nat _
      (nvec_zero (List.length tail))). split; cbn.
    + rewrite generated_input_zero, nvec_scale_one,
        nvec_add_zero_right_local. reflexivity.
    + rewrite generated_output_zero, nvec_scale_one,
        nvec_add_zero_right_local. reflexivity.
  - destruct (IH input output Hin) as [coefficients [Hinput Houtput]].
    exists (@Vector.cons nat 0%nat _ coefficients). split; cbn.
    + rewrite nvec_scale_zero, nvec_add_zero_left_local. exact Hinput.
    + rewrite nvec_scale_zero, nvec_add_zero_left_local. exact Houtput.
Qed.

Lemma generated_period_pairs_finitely_generated : forall d
    (generators : list (NVec d * NVec d)),
    FinitelyGeneratedPeriodic
      (ZRelationPairs (NRelationAsZ (@GeneratedPeriodPair d generators))).
Proof.
  intros d generators. exists (generated_period_zgenerators generators). split.
  - intros generator Hin. unfold generated_period_zgenerators in Hin.
    apply in_map_iff in Hin as [[input output] [<- Hin]].
    unfold ZRelationPairs. rewrite zpair_left_pack, zpair_right_pack.
    exists input, output. repeat split; try reflexivity.
    now apply generated_period_pair_generator.
  - intro pair. unfold zvec_generated, generated_period_zgenerators.
    rewrite List.length_map. split.
    + unfold ZRelationPairs, NRelationAsZ.
      intros [input [output [Hinput [Houtput [coefficients Hgenerated]]]]].
      pose proof (generated_period_linear_combination d generators coefficients)
        as Hcombination. unfold generated_period_zgenerators in Hcombination.
      exists coefficients. rewrite Hcombination.
      destruct Hgenerated as [Hgenerated_input Hgenerated_output].
      rewrite Hgenerated_input, Hgenerated_output, <- Hinput, <- Houtput,
        zpair_pack_split. reflexivity.
    + intros [coefficients Hpair]. unfold ZRelationPairs, NRelationAsZ.
      pose proof (generated_period_linear_combination d generators coefficients)
        as Hcombination. unfold generated_period_zgenerators in Hcombination.
      exists (GeneratedInput generators coefficients),
        (GeneratedOutput generators coefficients). repeat split.
      * rewrite <- zpair_left_pack with
          (right := nvec_to_zvec (GeneratedOutput generators coefficients)).
        rewrite <- Hcombination, Hpair. reflexivity.
      * rewrite <- zpair_right_pack with
          (left := nvec_to_zvec (GeneratedInput generators coefficients)).
        rewrite <- Hcombination, Hpair. reflexivity.
      * exists coefficients. split; reflexivity.
Qed.

Theorem generated_period_pair_asymptotically_definable : forall d
    (generators : list (NVec d * NVec d)),
    AsymptoticallyDefinableNRelation (@GeneratedPeriodPair d generators).
Proof.
  intros d generators. split.
  - apply generated_period_pair_periodic.
  - apply rational_polyhedral_cone_qdefinable.
    apply finitely_generated_period_cone_polyhedral.
    + apply periodic_zrelation_pairs_iff, periodic_nrelation_as_z,
        generated_period_pair_periodic.
    + apply generated_period_pairs_finitely_generated.
Qed.
