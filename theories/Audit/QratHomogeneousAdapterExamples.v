From Coq Require Import Fin Lia List QArith.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From Polyhedra Require Import polyhedron lrel inner_product.
From Mell.Geometry Require Import MathCompBridge Faces QConeCore LatticeGordanV
  QratAdapter QratVectorAdapter QratConeAdapter QratHomogeneousAdapter.

Import GRing.Theory Num.Theory Order.Theory ListNotations.
Set Printing Implicit.
Open Scope ring_scope.

Check @rat_cone_finite_base.
Check @rat_cone_contains_zero.
Check @rat_cone_scale_nonnegative.
Check @rat_cone_constraint_threshold_nonpositive.
Check @rat_cone_constraint_homogeneous.
Check @rat_cone_homogeneous_base.
Check @rat_col_qinner.
Check @rat_col_qinner_nonnegative_iff.
Check @polyhedra_cone_homogeneous_base.

Definition c_vec1 (value : Q) : QVec 1 := fun _ => value.
Definition c_one := c_vec1 (1 : Q).
Definition c_two := c_vec1 (2 : Q).
Definition c_minus_one := c_vec1 (-1 : Q).
Definition c_half := c_vec1 (Qmake 1 2%positive).
Definition c_two_fourths := c_vec1 (Qmake 2 4%positive).

Definition c_pair (left right : Q) : QVec 2 :=
  fun index => Fin.caseS' index (fun _ => Q) left (fun _ => right).
Definition c_e1 := c_pair 1 0.
Definition c_e2 := c_pair 0 1.
Definition c_zero2 := c_pair 0 0.

Example dimension_zero_homogeneous_base :
    exists normals : list (QVec 0),
      forall value : QVec 0,
        qcone_generated [] value <->
        forall normal, List.In normal normals -> Qle 0 (qinner normal value).
Proof. apply polyhedra_cone_homogeneous_base. Qed.

Example empty_generators_homogeneous_base :
    exists normals : list (QVec 1),
      forall value : QVec 1,
        qcone_generated [] value <->
        forall normal, List.In normal normals -> Qle 0 (qinner normal value).
Proof. apply polyhedra_cone_homogeneous_base. Qed.

Example empty_cone_is_exactly_zero : forall value : QVec 1,
    qcone_generated [] value <-> QVecEq value (qvec_zero 1).
Proof.
  intro value. split.
  - move/qcone_generated_aligned_coefficients=>
      [coefficients [Hlength [_ Hvalue]]].
    destruct coefficients; [exact Hvalue|discriminate].
  - intro Hvalue.
    apply (proj2 (qcone_generated_qvec_ext 1 [] value (qvec_zero 1) Hvalue)).
    apply qcone_generated_zero.
Qed.

Example zero_cone_homogeneous_base :
    exists normals : list (QVec 2),
      forall value : QVec 2,
        qcone_generated [c_zero2] value <->
        forall normal, List.In normal normals -> Qle 0 (qinner normal value).
Proof. apply polyhedra_cone_homogeneous_base. Qed.

Example full_line_homogeneous_base :
    exists normals : list (QVec 1),
      forall value : QVec 1,
        qcone_generated [c_one; c_minus_one] value <->
        forall normal, List.In normal normals -> Qle 0 (qinner normal value).
Proof. apply polyhedra_cone_homogeneous_base. Qed.

Example positive_ray_homogeneous_base :
    exists normals : list (QVec 1),
      forall value : QVec 1,
        qcone_generated [c_one] value <->
        forall normal, List.In normal normals -> Qle 0 (qinner normal value).
Proof. apply polyhedra_cone_homogeneous_base. Qed.

Example negative_ray_homogeneous_base :
    exists normals : list (QVec 1),
      forall value : QVec 1,
        qcone_generated [c_minus_one] value <->
        forall normal, List.In normal normals -> Qle 0 (qinner normal value).
Proof. apply polyhedra_cone_homogeneous_base. Qed.

Example orthant_homogeneous_base :
    exists normals : list (QVec 2),
      forall value : QVec 2,
        qcone_generated [c_e1; c_e2] value <->
        forall normal, List.In normal normals -> Qle 0 (qinner normal value).
Proof. apply polyhedra_cone_homogeneous_base. Qed.

Example full_plane_homogeneous_base :
    exists normals : list (QVec 2),
      forall value : QVec 2,
        qcone_generated [c_e1; qvec_scale (-1) c_e1;
          c_e2; qvec_scale (-1) c_e2] value <->
        forall normal, List.In normal normals -> Qle 0 (qinner normal value).
Proof. apply polyhedra_cone_homogeneous_base. Qed.

Example redundant_nonnormalized_homogeneous_base :
    exists normals : list (QVec 1),
      forall value : QVec 1,
        qcone_generated [c_half; c_two_fourths; c_one; c_two; c_one] value <->
        forall normal, List.In normal normals -> Qle 0 (qinner normal value).
Proof. apply polyhedra_cone_homogeneous_base. Qed.

Lemma low_rank_ray_excludes_transverse : ~ qcone_generated [c_e1] c_e2.
Proof.
  intro Hcone.
  apply qcone_generated_aligned_coefficients in Hcone as
    [coefficients [Hlength [_ Hvalue]]].
  destruct coefficients as [|coefficient [|extra coefficients]];
    simpl in Hlength; try discriminate.
  specialize (Hvalue (Fin.FS Fin.F1)).
  unfold c_e1, c_e2, c_pair, qlinear_combination,
    qvec_add, qvec_scale, qvec_zero in Hvalue.
  unfold Qeq in Hvalue. cbn in Hvalue. lia.
Qed.

Example low_rank_hrep_excludes_transverse :
    exists normals : list (QVec 2),
      (forall value : QVec 2,
        qcone_generated [c_e1] value <->
        forall normal, List.In normal normals -> Qle 0 (qinner normal value)) /\
      ~ (forall normal, List.In normal normals -> Qle 0 (qinner normal c_e2)).
Proof.
  destruct (polyhedra_cone_homogeneous_base [c_e1]) as [normals Hnormals].
  exists normals. split; [exact Hnormals|].
  intro Hall. apply low_rank_ray_excludes_transverse.
  apply (proj2 (Hnormals c_e2)). exact Hall.
Qed.

Example cone_zero_is_present :
    qvec_to_rat_col (qvec_zero 2) \in
      polyhedron.cone (rat_fset_of_generators [c_e1; c_e2]).
Proof.
  rewrite qvec_to_rat_col_zero /rat_fset_of_generators.
  apply rat_cone_contains_zero.
Qed.

Example cone_closed_under_nonnegative_scaling : forall scalar value,
    is_true (((0 : rat) <= scalar)%R) ->
    qvec_to_rat_col value \in polyhedron.cone (rat_fset_of_generators [c_e1]) ->
    scalar *: qvec_to_rat_col value \in
      polyhedron.cone (rat_fset_of_generators [c_e1]).
Proof. intros scalar value Hscalar Hvalue. exact (rat_cone_scale_nonnegative Hscalar Hvalue). Qed.

Lemma zero_normal_constraint_homogenized : forall d
    (columns : list ('cV[rat]_d)) (threshold : rat) (value : 'cV[rat]_d),
    is_true ((threshold <= (0 : rat))%R) ->
    value \in polyhedron.cone (rat_fset_of_columns columns) ->
    is_true (((0 : rat) <=
      @inner_product.vdot d rat_realFieldType (0 : 'cV[rat]_d) value)%R).
Proof.
  intros d columns threshold value Hthreshold Hvalue.
  destruct (rat_cone_finite_base columns) as [base Hbase].
  pose redundant : lrel[rat]_d := [<(0 : 'cV[rat]_d), threshold>].
  pose augmented : base_t[rat,d] := (base `|` [fset redundant])%fset.
  have Haugmented : forall candidate : 'cV[rat]_d,
      candidate \in polyhedron.cone (rat_fset_of_columns columns) <->
      forall constraint : lrel[rat]_d,
        constraint \in augmented ->
        is_true ((constraint.2 <=
          @inner_product.vdot d rat_realFieldType constraint.1 candidate)%R).
  { intro candidate. split.
    - intros Hcandidate constraint Hconstraint.
      rewrite /augmented in_fsetU in Hconstraint.
      move/orP: Hconstraint => [Horiginal|Hredundant].
      + exact (proj1 (Hbase candidate) Hcandidate constraint Horiginal).
      + rewrite in_fset1 in Hredundant. move/eqP: Hredundant => ->.
        rewrite /redundant /= vdot0l. exact Hthreshold.
    - intros Hall. apply (proj2 (Hbase candidate)).
      intros constraint Hconstraint. apply Hall.
      rewrite /augmented in_fsetU. apply/orP. now left. }
  apply (@rat_cone_constraint_homogeneous d columns augmented redundant
    Haugmented).
  - rewrite /augmented in_fsetU. apply/orP. right.
    by rewrite in_fset1 eqxx.
  - exact Hvalue.
Qed.

Example negative_affine_threshold_homogenized : forall value,
    value \in polyhedron.cone (rat_fset_of_generators [c_e1]) ->
    is_true (((0 : rat) <=
      @inner_product.vdot 2 rat_realFieldType (0 : 'cV[rat]_2) value)%R).
Proof.
  intros value Hvalue.
  apply (@zero_normal_constraint_homogenized 2
    (rat_cols_of_list [c_e1]) (-1 : rat) value).
  - exact (lerN10 rat_numDomainType).
  - exact Hvalue.
Qed.

Example zero_affine_threshold_homogenized : forall value,
    value \in polyhedron.cone (rat_fset_of_generators [c_e1]) ->
    is_true (((0 : rat) <=
      @inner_product.vdot 2 rat_realFieldType (0 : 'cV[rat]_2) value)%R).
Proof.
  intros value Hvalue.
  apply (@zero_normal_constraint_homogenized 2
    (rat_cols_of_list [c_e1]) (0 : rat) value).
  - exact: lexx.
  - exact Hvalue.
Qed.

Print Assumptions rat_cone_finite_base.
Print Assumptions rat_cone_contains_zero.
Print Assumptions rat_cone_scale_nonnegative.
Print Assumptions rat_cone_constraint_threshold_nonpositive.
Print Assumptions rat_cone_constraint_homogeneous.
Print Assumptions rat_cone_homogeneous_base.
Print Assumptions rat_col_qinner.
Print Assumptions rat_col_qinner_nonnegative_iff.
Print Assumptions polyhedra_cone_homogeneous_base.
