From Coq Require Import List QArith.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From Polyhedra Require Import polyhedron barycenter inner_product lrel.
From Mell.Geometry Require Import MathCompBridge QConeCore Faces
  QratAdapter QratVectorAdapter QratConeAdapter.

Import GRing.Theory Num.Theory Order.Theory.
Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Theorem rat_cone_finite_base : forall d
    (columns : list ('cV[rat]_d)),
    exists base : base_t[rat,d],
      forall value : 'cV[rat]_d,
        value \in polyhedron.cone (rat_fset_of_columns columns) <->
        forall constraint : lrel[rat]_d,
          constraint \in base ->
          is_true ((constraint.2 <= '[constraint.1, value])%R).
Proof.
  intros d columns.
  destruct (polyhedron.is_poly_of_base
    (polyhedron.cone (rat_fset_of_columns columns))) as [base Hbase].
  exists base. intro value. split.
  - intro Hvalue. move/eqP: Hbase => Hbase. rewrite Hbase in Hvalue.
    move/polyhedron.in_poly_of_baseP: Hvalue => Hvalue constraint Hconstraint.
    move: (Hvalue constraint Hconstraint).
    by rewrite polyhedron.in_hs.
  - intro Hconstraints. move/eqP: Hbase => Hbase. rewrite Hbase.
    apply/polyhedron.in_poly_of_baseP=> constraint Hconstraint.
    rewrite polyhedron.in_hs. exact (Hconstraints constraint Hconstraint).
Qed.

Lemma rat_linear_combination_zero_coefficients : forall d
    (columns : list ('cV[rat]_d)),
    rat_linear_combination columns
      (List.map (fun _ => (0 : rat)) columns) = 0.
Proof.
  intros d columns. induction columns as [|column columns IH]; simpl.
  - reflexivity.
  - by rewrite scale0r add0r IH.
Qed.

Lemma rat_linear_combination_scale_coefficients : forall d
    (columns : list ('cV[rat]_d)) (coefficients : list rat) (scalar : rat),
    List.length columns = List.length coefficients ->
    rat_linear_combination columns
      (List.map (fun coefficient => scalar * coefficient) coefficients) =
    scalar *: rat_linear_combination columns coefficients.
Proof.
  intros d columns. induction columns as [|column columns IH];
    intros [|coefficient coefficients] scalar Hlength;
    simpl in *; try discriminate.
  - by rewrite scaler0.
  - inversion Hlength as [Htail].
    rewrite IH; last exact Htail.
    by rewrite scalerDr scalerA.
Qed.

Lemma rat_scale_coefficients_nonnegative : forall (scalar : rat)
    coefficients,
    is_true (((0 : rat) <= scalar)%R) ->
    List.Forall
      (fun coefficient => is_true (((0 : rat) <= coefficient)%R))
      coefficients ->
    List.Forall
      (fun coefficient => is_true (((0 : rat) <= coefficient)%R))
      (List.map (fun coefficient => scalar * coefficient) coefficients).
Proof.
  intros scalar coefficients Hscalar Hall.
  induction Hall as [|coefficient coefficients Hcoefficient Htail IH].
  - constructor.
  - simpl. constructor; [exact (mulr_ge0 Hscalar Hcoefficient)|exact IH].
Qed.

Theorem rat_cone_contains_zero : forall d
    (columns : list ('cV[rat]_d)),
    (0 : 'cV[rat]_d) \in
      polyhedron.cone (rat_fset_of_columns columns).
Proof.
  intros d columns.
  apply (proj2 (rat_columns_polyhedra_cone columns (0 : 'cV[rat]_d))).
  exists (List.map (fun _ => (0 : rat)) columns). repeat split.
  - apply List.length_map.
  - induction columns as [|column columns IH]; simpl; constructor.
    + exact: lexx.
    + exact IH.
  - symmetry. apply rat_linear_combination_zero_coefficients.
Qed.

Theorem rat_cone_scale_nonnegative : forall d
    (columns : list ('cV[rat]_d)) (scalar : rat) (value : 'cV[rat]_d),
    is_true (((0 : rat) <= scalar)%R) ->
    value \in polyhedron.cone (rat_fset_of_columns columns) ->
    scalar *: value \in polyhedron.cone (rat_fset_of_columns columns).
Proof.
  intros d columns scalar value Hscalar Hvalue.
  apply (proj1 (rat_columns_polyhedra_cone columns value)) in Hvalue.
  destruct Hvalue as [coefficients [Hlength [Hnonnegative Hvalue]]].
  apply (proj2 (rat_columns_polyhedra_cone columns (scalar *: value))).
  exists (List.map (fun coefficient => scalar * coefficient) coefficients).
  repeat split.
  - rewrite List.length_map. exact Hlength.
  - now apply rat_scale_coefficients_nonnegative.
  - rewrite Hvalue. symmetry.
    apply rat_linear_combination_scale_coefficients.
    symmetry. exact Hlength.
Qed.

Lemma list_in_mathcomp_mem : forall (T : eqType) (value : T) values,
    List.In value values -> value \in values.
Proof.
  intros T value values. induction values as [|head tail IH]; intro Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst value. by rewrite in_cons eqxx.
    + rewrite in_cons. apply/orP. right. exact (IH Hin).
Qed.

Lemma mathcomp_mem_list_in : forall (T : eqType) (value : T) values,
    value \in values -> List.In value values.
Proof.
  intros T value values. induction values as [|head tail IH]; intro Hin.
  - discriminate.
  - rewrite in_cons in Hin. move/orP: Hin => [/eqP Heq|Hin].
    + now left.
    + right. exact (IH Hin).
Qed.

Lemma rat_cone_constraint_threshold_nonpositive : forall d
    (columns : list ('cV[rat]_d)) (base : base_t[rat,d])
    (constraint : lrel[rat]_d),
    (forall value : 'cV[rat]_d,
      value \in polyhedron.cone (rat_fset_of_columns columns) <->
      forall candidate : lrel[rat]_d,
        candidate \in base ->
        is_true ((candidate.2 <= '[candidate.1, value])%R)) ->
    constraint \in base ->
    is_true ((constraint.2 <= (0 : rat))%R).
Proof.
  intros d columns base constraint Hbase Hconstraint.
  have Hzero := proj1 (Hbase (0 : 'cV[rat]_d))
    (rat_cone_contains_zero columns).
  have := Hzero constraint Hconstraint.
  by rewrite vdot0r.
Qed.

Lemma rat_cone_constraint_homogeneous : forall d
    (columns : list ('cV[rat]_d)) (base : base_t[rat,d])
    (constraint : lrel[rat]_d),
    (forall value : 'cV[rat]_d,
      value \in polyhedron.cone (rat_fset_of_columns columns) <->
      forall candidate : lrel[rat]_d,
        candidate \in base ->
        is_true ((candidate.2 <= '[candidate.1, value])%R)) ->
    constraint \in base ->
    forall value : 'cV[rat]_d,
      value \in polyhedron.cone (rat_fset_of_columns columns) ->
      is_true (((0 : rat) <= '[constraint.1, value])%R).
Proof.
  intros d columns base constraint Hbase Hconstraint value Hvalue.
  case: (lerP (0 : rat) '[constraint.1, value]) => Hnonnegative.
  - by [].
  - have Hthreshold : is_true ((constraint.2 <= (0 : rat))%R).
    { exact (rat_cone_constraint_threshold_nonpositive Hbase Hconstraint). }
    pose scalar : rat :=
      ((1 : rat) - constraint.2) / (- '[constraint.1, value]).
    have Hnumerator : is_true (((0 : rat) < 1 - constraint.2)%R).
    { rewrite subr_gt0. exact (le_lt_trans Hthreshold ltr01). }
    have Hdenominator : is_true (((0 : rat) < - '[constraint.1, value])%R).
    { by rewrite oppr_gt0. }
    have Hscalar_positive : is_true (((0 : rat) < scalar)%R).
    { exact (divr_gt0 Hnumerator Hdenominator). }
    have Hscaled := @rat_cone_scale_nonnegative d columns scalar value
      (ltW Hscalar_positive) Hvalue.
    have Hscaled_constraint :=
      proj1 (Hbase (scalar *: value)) Hscaled constraint Hconstraint.
    rewrite vdotZr in Hscaled_constraint.
    have Hscaled_inner :
        scalar * '[constraint.1, value] = constraint.2 - 1.
    { rewrite /scalar.
      have Hinner_opp : '[constraint.1, value] =
          - (- '[constraint.1, value]) by rewrite opprK.
      rewrite [X in _ * X]Hinner_opp
        mulrN divfK; last exact (lt0r_neq0 Hdenominator).
      by rewrite opprB. }
    rewrite Hscaled_inner in Hscaled_constraint.
    have Hbad : constraint.2 + 1 <= constraint.2.
    { by move: Hscaled_constraint; rewrite ler_subr_addr. }
    have Hincrease : constraint.2 < constraint.2 + 1.
    { exact (ltr_spaddr ltr01 (lexx constraint.2)). }
    have Hfalse : constraint.2 < constraint.2 :=
      lt_le_trans Hincrease Hbad.
    by rewrite ltxx in Hfalse.
Qed.

Theorem rat_cone_homogeneous_base : forall d
    (columns : list ('cV[rat]_d)),
    exists normals : list ('cV[rat]_d),
      forall value : 'cV[rat]_d,
        value \in polyhedron.cone (rat_fset_of_columns columns) <->
        forall normal : 'cV[rat]_d,
          List.In normal normals ->
          is_true (((0 : rat) <= '[normal, value])%R).
Proof.
  intros d columns.
  destruct (rat_cone_finite_base columns) as [base Hbase].
  exists (List.map (fun constraint : lrel[rat]_d => constraint.1)
    (enum_fset base)).
  intro value. split.
  - intros Hvalue normal Hnormal.
    apply List.in_map_iff in Hnormal.
    destruct Hnormal as [constraint [Hnormal Hconstraint]].
    subst normal.
    apply (rat_cone_constraint_homogeneous Hbase).
    + exact (list_in_mathcomp_mem Hconstraint).
    + exact Hvalue.
  - intros Hnormals. apply (proj2 (Hbase value)).
    intros constraint Hconstraint.
    have Hthreshold :=
      rat_cone_constraint_threshold_nonpositive Hbase Hconstraint.
    have Hconstraint_list : List.In constraint (enum_fset base).
    { apply mathcomp_mem_list_in. exact Hconstraint. }
    have Hnormal_list : List.In constraint.1
        (List.map (fun candidate : lrel[rat]_d => candidate.1)
          (enum_fset base)).
    { apply List.in_map_iff. exists constraint. split.
      - reflexivity.
      - exact Hconstraint_list. }
    have Hnormal := Hnormals constraint.1 Hnormal_list.
    exact (le_trans Hthreshold Hnormal).
Qed.

Lemma rat_col_qinner : forall d (normal : 'cV[rat]_d)
    (value : QVec d),
    q_to_rat (qinner (rat_col_to_qvec normal) value) =
      '[normal, qvec_to_rat_col value].
Proof.
  intros d normal value.
  rewrite q_to_rat_qinner qvec_to_rat_row_transpose
    rat_col_to_qvec_roundtrip.
  rewrite mxE /vdot.
  apply eq_bigr. intros index _. by rewrite !mxE.
Qed.

Lemma rat_col_qinner_nonnegative_iff : forall d
    (normal : 'cV[rat]_d) (value : QVec d),
    Qle 0 (qinner (rat_col_to_qvec normal) value) <->
      is_true (((0 : rat) <= '[normal, qvec_to_rat_col value])%R).
Proof.
  intros d normal value. rewrite <- rat_col_qinner.
  apply q_to_rat_nonnegative_iff.
Qed.

Theorem polyhedra_cone_homogeneous_base : forall d
    (generators : list (QVec d)),
    exists normals : list (QVec d),
      forall value : QVec d,
        qcone_generated generators value <->
        forall normal : QVec d,
          List.In normal normals -> Qle 0 (qinner normal value).
Proof.
  intros d generators.
  destruct (@rat_cone_homogeneous_base d (rat_cols_of_list generators))
    as [rat_normals Hrat].
  exists (List.map rat_col_to_qvec rat_normals).
  intro value. rewrite qcone_generated_polyhedra_cone
    /rat_fset_of_generators Hrat. split.
  - intros Hnormals normal Hnormal.
    apply List.in_map_iff in Hnormal.
    destruct Hnormal as [rat_normal [Hnormal Hin]]. subst normal.
    apply (proj2 (rat_col_qinner_nonnegative_iff rat_normal value)).
    exact (Hnormals rat_normal Hin).
  - intros Hnormals rat_normal Hin.
    apply (proj1 (rat_col_qinner_nonnegative_iff rat_normal value)).
    apply Hnormals. apply List.in_map. exact Hin.
Qed.
