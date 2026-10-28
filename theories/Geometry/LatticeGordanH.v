From Coq Require Import List Vector VectorSpec ZArith QArith Qring Lia.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge Periodic QConeCore RationalHToV.
From Mell.Semilinear Require Import LinearEquations Presentation.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.

Definition zvec_zsmul {d} (coefficient : Z) (value : ZVec d) : ZVec d :=
  Vector.map (Z.mul coefficient) value.

Fixpoint zgroup_combination {d} (generators : list (ZVec d)) :
    Vector.t Z (length generators) -> ZVec d :=
  match generators as generators0 return
      Vector.t Z (length generators0) -> ZVec d with
  | [] => fun _ => zvec_zero d
  | generator :: generators' => fun coefficients =>
      zvec_add (zvec_zsmul (Vector.hd coefficients) generator)
        (zgroup_combination generators' (Vector.tl coefficients))
  end.

Definition ZGroupGenerated {d} (generators : list (ZVec d))
    (value : ZVec d) : Prop :=
  exists coefficients : Vector.t Z (length generators),
    zgroup_combination generators coefficients = value.

Lemma zvec_zsmul_nth : forall d coefficient (value : ZVec d) index,
    Vector.nth (zvec_zsmul coefficient value) index =
      (coefficient * Vector.nth value index)%Z.
Proof.
  intros. unfold zvec_zsmul.
  now rewrite (nth_map _ _ index index eq_refl).
Qed.

Lemma zvec_zsmul_zero : forall d (value : ZVec d),
    zvec_zsmul 0%Z value = zvec_zero d.
Proof.
  intros d value. apply zvec_ext. intro index.
  rewrite zvec_zsmul_nth. unfold zvec_zero.
  rewrite (const_nth Z 0%Z d index). lia.
Qed.

Lemma zvec_zsmul_add : forall d left right (value : ZVec d),
    zvec_zsmul (left + right) value =
      zvec_add (zvec_zsmul left value) (zvec_zsmul right value).
Proof.
  intros d left right value. induction value as [|head d tail IH].
  - reflexivity.
  - cbn. f_equal; [ring|exact IH].
Qed.

Lemma zvec_zsmul_nat : forall d coefficient (value : ZVec d),
    zvec_zsmul (Z.of_nat coefficient) value = zvec_nsmul coefficient value.
Proof.
  intros d coefficient value. apply zvec_ext. intro index.
  rewrite zvec_zsmul_nth, nth_zvec_nsmul. reflexivity.
Qed.

Lemma zgroup_combination_zero : forall d (generators : list (ZVec d)),
    zgroup_combination generators
      (Vector.const 0%Z (length generators)) = zvec_zero d.
Proof.
  intros d generators. induction generators as [|generator generators IH].
  - reflexivity.
  - cbn. rewrite zvec_zsmul_zero, IH, zvec_add_zero_left. reflexivity.
Qed.

Lemma zgroup_combination_add : forall d (generators : list (ZVec d))
    (left right : Vector.t Z (length generators)),
    zgroup_combination generators (Vector.map2 Z.add left right) =
      zvec_add (zgroup_combination generators left)
        (zgroup_combination generators right).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intro left; intro right.
  - refine (Vector.case0 (fun left =>
      zgroup_combination [] (Vector.map2 Z.add left right) =
      zvec_add (zgroup_combination [] left)
        (zgroup_combination [] right)) _ left).
    refine (Vector.case0 (fun right =>
      zgroup_combination [] (Vector.map2 Z.add (@Vector.nil Z) right) =
      zvec_add (zgroup_combination [] (@Vector.nil Z))
        (zgroup_combination [] right)) _ right).
    cbn. symmetry. apply zvec_add_zero_right.
  - revert right.
    refine (Vector.caseS' left (fun left => forall right,
      zgroup_combination (generator :: generators)
        (Vector.map2 Z.add left right) =
      zvec_add (zgroup_combination (generator :: generators) left)
        (zgroup_combination (generator :: generators) right)) _).
    intros left_head left_tail right.
    refine (Vector.caseS' right (fun right =>
      zgroup_combination (generator :: generators)
        (Vector.map2 Z.add (@Vector.cons Z left_head _ left_tail) right) =
      zvec_add
        (zgroup_combination (generator :: generators)
          (@Vector.cons Z left_head _ left_tail))
        (zgroup_combination (generator :: generators) right)) _).
    intros right_head right_tail. cbn.
    rewrite zvec_zsmul_add, IH.
    repeat rewrite <- zvec_add_assoc.
    f_equal. rewrite zvec_add_assoc,
      (zvec_add_comm d (zvec_zsmul right_head generator)),
      <- zvec_add_assoc. reflexivity.
Qed.

Lemma zgroup_combination_nat_scale : forall d
    (generators : list (ZVec d)) coefficient
    (value : Vector.t Z (length generators)),
    zgroup_combination generators
      (Vector.map (Z.mul (Z.of_nat coefficient)) value) =
    zvec_nsmul coefficient (zgroup_combination generators value).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficient value.
  - refine (Vector.case0 (fun value => _) _ value). cbn.
    apply zvec_ext. intro index. rewrite nth_zvec_nsmul.
    unfold zvec_zero. rewrite (const_nth Z 0%Z d index). ring.
  - refine (Vector.caseS' value (fun value => _) _).
    intros head tail.
    change (zvec_add
      (zvec_zsmul (Z.of_nat coefficient * head) generator)
      (zgroup_combination generators
        (Vector.map (Z.mul (Z.of_nat coefficient)) tail)) =
      zvec_nsmul coefficient
        (zvec_add (zvec_zsmul head generator)
          (zgroup_combination generators tail))).
    rewrite IH.
    apply zvec_ext. intro index.
    rewrite nth_zvec_nsmul. unfold zvec_add.
    repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
    rewrite !zvec_zsmul_nth, nth_zvec_nsmul. ring.
Qed.

Lemma zgroup_generated_periodic : forall d (generators : list (ZVec d)),
    Periodic (@ZGroupGenerated d generators).
Proof.
  intros d generators. split.
  - exists (Vector.const 0%Z (length generators)).
    apply zgroup_combination_zero.
  - intros left right [left_coefficients <-] [right_coefficients <-].
    exists (Vector.map2 Z.add left_coefficients right_coefficients).
    apply zgroup_combination_add.
Qed.

Fixpoint qgroup_combination {d} (generators : list (ZVec d)) :
    Vector.t Q (length generators) -> QVec d :=
  match generators as generators0 return
      Vector.t Q (length generators0) -> QVec d with
  | [] => fun _ => qvec_zero d
  | generator :: generators' => fun coefficients =>
      qvec_add
        (qvec_scale (Vector.hd coefficients) (zvec_to_qvec generator))
        (qgroup_combination generators' (Vector.tl coefficients))
  end.

Fixpoint pulled_row {d} (row : Vector.t Q d)
    (generators : list (ZVec d)) : Vector.t Q (length generators) :=
  match generators with
  | [] => @Vector.nil Q
  | generator :: generators' =>
      @Vector.cons Q (qrow_apply row (zvec_to_qvec generator)) _
        (pulled_row row generators')
  end.

Definition pulled_qmatrix {rows d} (matrix : QMatrix rows d)
    (generators : list (ZVec d)) : QMatrix rows (length generators) :=
  Vector.map (fun row => pulled_row row generators) matrix.

Lemma qgroup_combination_inject : forall d (generators : list (ZVec d))
    (coefficients : Vector.t Z (length generators)),
    QVecEq
      (qgroup_combination generators (Vector.map inject_Z coefficients))
      (zvec_to_qvec (zgroup_combination generators coefficients)).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intro coefficients.
  - refine (Vector.case0 (fun coefficients => _) _ coefficients).
    intro index.
    change (0 == inject_Z (Vector.nth (Vector.const 0%Z d) index)).
    rewrite (const_nth Z 0%Z d index). reflexivity.
  - refine (Vector.caseS' coefficients (fun coefficients => _) _).
    intros head tail index. cbn.
    unfold qvec_add, qvec_scale, zvec_to_qvec, zvec_add.
    rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl),
      inject_Z_plus, zvec_zsmul_nth, inject_Z_mult.
    specialize (IH tail index). cbn in IH.
    apply Qplus_comp; [reflexivity|exact IH].
Qed.

Lemma qdot_pulled_row : forall d (row : Vector.t Q d)
    (generators : list (ZVec d))
    (coefficients : Vector.t Q (length generators)),
    qdot (pulled_row row generators) coefficients ==
      qrow_apply row (qgroup_combination generators coefficients).
Proof.
  intros d row generators. induction generators as [|generator generators IH];
    intro coefficients.
  - refine (Vector.case0 (fun coefficients => _) _ coefficients).
    cbn. symmetry. apply qrow_apply_zero.
  - refine (Vector.caseS' coefficients (fun coefficients => _) _).
    intros head tail.
    change (qrow_apply row (zvec_to_qvec generator) * head +
      qdot (pulled_row row generators) tail ==
      qrow_apply row
        (qvec_add (qvec_scale head (zvec_to_qvec generator))
          (qgroup_combination generators tail))).
    transitivity (head * qrow_apply row (zvec_to_qvec generator) +
      qrow_apply row (qgroup_combination generators tail)).
    + apply Qplus_comp; [ring|apply IH].
    + symmetry. eapply Qeq_trans; [apply qrow_apply_add|].
      apply Qplus_comp; [apply qrow_apply_scale|reflexivity].
Qed.

Lemma pulled_row_apply : forall d (row : Vector.t Q d)
    (generators : list (ZVec d))
    (coefficients : Vector.t Z (length generators)),
    qrow_apply (pulled_row row generators) (zvec_to_qvec coefficients) ==
      qrow_apply row
        (zvec_to_qvec (zgroup_combination generators coefficients)).
Proof.
  intros d row generators coefficients. unfold qrow_apply.
  transitivity (qdot (pulled_row row generators)
    (Vector.map inject_Z coefficients)).
  - apply qdot_ext; [intro index; reflexivity|]. intro index.
    rewrite qvec_to_vector_nth,
      (nth_map _ _ index index eq_refl). reflexivity.
  - setoid_rewrite qdot_pulled_row.
    apply qrow_apply_qvec_ext.
    apply qgroup_combination_inject.
Qed.

Lemma pulled_constraints_iff : forall rows d (matrix : QMatrix rows d)
    generators coefficients,
    HConicalConstraints (pulled_qmatrix matrix generators)
      (zvec_to_qvec coefficients) <->
    HConicalConstraints matrix
      (zvec_to_qvec (zgroup_combination generators coefficients)).
Proof.
  intros rows d matrix generators coefficients. split; intros H row.
  - specialize (H row). unfold pulled_qmatrix in H.
    rewrite (nth_map _ _ row row eq_refl) in H.
    setoid_rewrite (pulled_row_apply d (Vector.nth matrix row)
      generators coefficients) in H. exact H.
  - specialize (H row). unfold pulled_qmatrix.
    rewrite (nth_map _ _ row row eq_refl).
    setoid_rewrite (pulled_row_apply d (Vector.nth matrix row)
      generators coefficients). exact H.
Qed.

Definition solution_coefficients {rows k}
    (value : NVec (k + (k + rows))) : ZVec k :=
  Vector.map2 (fun positive negative =>
    (Z.of_nat positive - Z.of_nat negative)%Z)
    (solution_positive value) (solution_negative value).

Lemma solution_coefficients_append : forall rows k
    (positive negative : NVec k) (slack : NVec rows) index,
    Vector.nth
      (solution_coefficients
        (Vector.append positive (Vector.append negative slack))) index =
      (Z.of_nat (Vector.nth positive index) -
        Z.of_nat (Vector.nth negative index))%Z.
Proof.
  intros. unfold solution_coefficients, solution_positive, solution_negative,
    solution_remainder, nvec_left, nvec_right.
  rewrite VectorSpec.splitat_append. cbn.
  rewrite VectorSpec.splitat_append.
  rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
  reflexivity.
Qed.

Lemma project_solution_coefficients : forall rows k
    (value : NVec (k + (k + rows))),
    QVecEq (project_solution value)
      (zvec_to_qvec (solution_coefficients value)).
Proof.
  intros rows k value index.
  pose proof (solution_three_parts rows k value) as Hparts.
  rewrite Hparts, project_solution_append.
  unfold zvec_to_qvec. rewrite solution_coefficients_append.
  unfold Qminus, Z.sub. rewrite <- inject_Z_opp, <- inject_Z_plus.
  reflexivity.
Qed.

Lemma solution_coefficients_zero : forall rows k,
    solution_coefficients (nvec_zero (k + (k + rows))) = zvec_zero k.
Proof.
  intros rows k. apply zvec_ext. intro index.
  assert (Hzero : nvec_zero (k + (k + rows)) =
      Vector.append (nvec_zero k)
        (Vector.append (nvec_zero k) (nvec_zero rows))).
  { unfold nvec_zero. symmetry.
    repeat rewrite VectorSpec.append_const. reflexivity. }
  rewrite Hzero, solution_coefficients_append.
  unfold nvec_zero, zvec_zero.
  rewrite !const_nth. reflexivity.
Qed.

Lemma solution_coefficients_add : forall rows k
    (left right : NVec (k + (k + rows))),
    solution_coefficients (nvec_add left right) =
      zvec_add (solution_coefficients left) (solution_coefficients right).
Proof.
  intros rows k left right. apply zvec_ext. intro index.
  unfold zvec_add.
  rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
  apply inject_Z_injective.
  eapply Qeq_trans.
  - symmetry. apply (project_solution_coefficients rows k
      (nvec_add left right) index).
  - eapply Qeq_trans.
    + apply (project_solution_add rows k left right index).
    + unfold qvec_add.
      eapply Qeq_trans.
      * apply Qplus_comp;
          apply (project_solution_coefficients rows k); exact index.
      * rewrite inject_Z_plus. reflexivity.
Qed.

Lemma solution_coefficients_scale : forall rows k coefficient
    (value : NVec (k + (k + rows))),
    solution_coefficients (nvec_scale coefficient value) =
      Vector.map (Z.mul (Z.of_nat coefficient))
        (solution_coefficients value).
Proof.
  intros rows k coefficient value. apply zvec_ext. intro index.
  rewrite (nth_map _ _ index index eq_refl).
  apply inject_Z_injective.
  eapply Qeq_trans.
  - symmetry. apply (project_solution_coefficients rows k
      (nvec_scale coefficient value) index).
  - eapply Qeq_trans.
    + apply (project_solution_scale rows k coefficient value index).
    + unfold qvec_scale, q_of_nat.
      eapply Qeq_trans.
      * apply Qmult_comp; [reflexivity|].
        apply (project_solution_coefficients rows k value index).
      * rewrite inject_Z_mult. reflexivity.
Qed.

Definition project_group_solution {rows d} (generators : list (ZVec d))
    (value : NVec (length generators + (length generators + rows))) : ZVec d :=
  zgroup_combination generators (solution_coefficients value).

Lemma project_group_solution_zero : forall rows d
    (generators : list (ZVec d)),
    project_group_solution (rows := rows) (d := d) generators
      (nvec_zero
        (length generators + (length generators + rows))) = zvec_zero d.
Proof.
  intros. unfold project_group_solution.
  rewrite solution_coefficients_zero, zgroup_combination_zero. reflexivity.
Qed.

Lemma project_group_solution_add : forall rows d
    (generators : list (ZVec d))
    (left right :
      NVec (length generators + (length generators + rows))),
    project_group_solution generators (nvec_add left right) =
      zvec_add (project_group_solution generators left)
        (project_group_solution generators right).
Proof.
  intros. unfold project_group_solution.
  rewrite solution_coefficients_add, zgroup_combination_add. reflexivity.
Qed.

Lemma project_group_solution_scale : forall rows d
    (generators : list (ZVec d)) coefficient
    (value : NVec (length generators + (length generators + rows))),
    project_group_solution generators (nvec_scale coefficient value) =
      zvec_nsmul coefficient (project_group_solution generators value).
Proof.
  intros. unfold project_group_solution.
  rewrite solution_coefficients_scale, zgroup_combination_nat_scale.
  reflexivity.
Qed.

Lemma project_group_solution_in_group : forall rows d
    (generators : list (ZVec d))
    (value : NVec (length generators + (length generators + rows))),
    ZGroupGenerated generators (project_group_solution generators value).
Proof.
  intros. exists (solution_coefficients value). reflexivity.
Qed.

Lemma project_group_solution_constraints : forall rows d
    (matrix : QMatrix rows d) (generators : list (ZVec d)) denominator
    (integer_matrix : ZMatrix rows (length generators))
    (Hpositive : (0 < denominator)%nat)
    (Hclear : forall row column,
      inject_Z (Vector.nth (Vector.nth integer_matrix row) column) ==
        q_of_nat denominator *
          Vector.nth
            (Vector.nth (pulled_qmatrix matrix generators) row) column)
    value,
    HomogeneousSolution (homogenized_matrix integer_matrix) value ->
    HConicalConstraints matrix
      (zvec_to_qvec (project_group_solution generators value)).
Proof.
  intros rows d matrix generators denominator integer_matrix Hpositive
    Hclear value Hsolution.
  assert (Hinteger : forall row,
      0 <= zrow_qapply (Vector.nth integer_matrix row)
        (project_solution value)).
  { now apply homogeneous_project_nonnegative. }
  assert (Hpulled : HConicalConstraints
      (pulled_qmatrix matrix generators) (project_solution value)).
  { apply (proj2 (cleared_matrix_constraints_iff rows
      (length generators) (pulled_qmatrix matrix generators)
      denominator integer_matrix Hpositive Hclear
      (project_solution value))).
    exact Hinteger. }
  assert (Hpulled_integer : HConicalConstraints
      (pulled_qmatrix matrix generators)
      (zvec_to_qvec (solution_coefficients value))).
  { apply (proj1 (hconstraints_qvec_ext rows (length generators)
      (pulled_qmatrix matrix generators)
      (project_solution value)
      (zvec_to_qvec (solution_coefficients value))
      (project_solution_coefficients rows (length generators) value))).
    exact Hpulled. }
  apply (proj1 (pulled_constraints_iff rows d matrix generators
    (solution_coefficients value))).
  exact Hpulled_integer.
Qed.

Lemma zvec_to_qvec_zero_local : forall d,
    QVecEq (zvec_to_qvec (zvec_zero d)) (qvec_zero d).
Proof.
  intros d index. unfold zvec_to_qvec, zvec_zero, qvec_zero.
  rewrite const_nth. reflexivity.
Qed.

Lemma hconstraints_integer_periodic : forall rows d
    (matrix : QMatrix rows d),
    Periodic (fun value : ZVec d =>
      HConicalConstraints matrix (zvec_to_qvec value)).
Proof.
  intros rows d matrix.
  pose proof (hconstraints_is_cone rows d matrix) as Hcone.
  split.
  - apply (proj2 (hconstraints_qvec_ext rows d matrix
      (zvec_to_qvec (zvec_zero d)) (qvec_zero d)
      (zvec_to_qvec_zero_local d))).
    exact (@cone_contains_zero d _ Hcone).
  - intros left right Hleft Hright.
    apply (proj2 (hconstraints_qvec_ext rows d matrix
      (zvec_to_qvec (zvec_add left right))
      (qvec_add (zvec_to_qvec left) (zvec_to_qvec right))
      (zvec_to_qvec_add d left right))).
    now apply (@cone_closed_add d _ Hcone).
Qed.

Lemma group_hcone_intersection_periodic : forall rows d
    (matrix : QMatrix rows d) (generators : list (ZVec d)),
    Periodic (fun value : ZVec d =>
      ZGroupGenerated generators value /\
      HConicalConstraints matrix (zvec_to_qvec value)).
Proof.
  intros rows d matrix generators.
  destruct (zgroup_generated_periodic d generators) as [Hgroup0 Hgroupadd].
  destruct (hconstraints_integer_periodic rows d matrix) as [Hcone0 Hconeadd].
  split.
  - split; assumption.
  - intros left right [Hleft_group Hleft_cone]
      [Hright_group Hright_cone]. split.
    + now apply Hgroupadd.
    + now apply Hconeadd.
Qed.

Lemma weighted_sum_project_group_generated : forall rows d
    (generators : list (ZVec d))
    (integer_generators :
      list (NVec
        (length generators + (length generators + rows))))
    coefficients value,
    weighted_sum coefficients integer_generators = Some value ->
    zvec_generated
      (List.map (@project_group_solution rows d generators)
        integer_generators)
      (project_group_solution generators value).
Proof.
  intros rows d generators integer_generators.
  induction integer_generators as [|generator integer_generators IH];
    intros coefficients value Hsum.
  - destruct coefficients; cbn in Hsum; try discriminate.
    inversion Hsum; subst value.
    rewrite project_group_solution_zero. apply generated_zero.
  - destruct coefficients as [|coefficient coefficients]; try discriminate.
    cbn in Hsum.
    destruct (weighted_sum coefficients integer_generators) as [tail|]
      eqn:Htail; try discriminate.
    inversion Hsum; subst value.
    rewrite project_group_solution_add, project_group_solution_scale.
    apply generated_add.
    + apply periodic_nsmul with
        (set := @zvec_generated d
          (List.map (@project_group_solution rows d generators)
            (generator :: integer_generators))).
      * apply generated_periodic.
      * apply generated_generator. cbn. now left.
    + apply generated_append_right with
        (left := [project_group_solution generators generator])
        (right := List.map
          (@project_group_solution rows d generators) integer_generators).
      apply IH with (coefficients := coefficients). exact Htail.
Qed.

Lemma project_group_integer_solution : forall rows d
    (generators : list (ZVec d))
    (coefficients : ZVec (length generators))
    (slack : NVec rows),
    project_group_solution generators
      (Vector.append (zvec_positive coefficients)
        (Vector.append (zvec_negative coefficients) slack)) =
      zgroup_combination generators coefficients.
Proof.
  intros rows d generators coefficients slack.
  unfold project_group_solution.
  f_equal. apply zvec_ext. intro index.
  rewrite solution_coefficients_append.
  apply zvec_positive_negative.
Qed.

Theorem lattice_gordan_hmatrix : forall d rows
    (matrix : QMatrix rows d) (generators : list (ZVec d)),
    FinitelyGeneratedPeriodic
      (fun value : ZVec d =>
        ZGroupGenerated generators value /\
        HConicalConstraints matrix (zvec_to_qvec value)).
Proof.
  intros d rows matrix generators.
  destruct (qmatrix_clear_denominators rows (length generators)
    (pulled_qmatrix matrix generators)) as
    [denominator [integer_matrix [Hpositive Hclear]]].
  destruct (homogeneous_solutions_finitely_generated rows
    (length generators + (length generators + rows))
    (homogenized_matrix integer_matrix)) as
    [integer_generators [Hgenerator_solution Hgenerated]].
  exists (List.map (@project_group_solution rows d generators)
    integer_generators). split.
  - intros generator Hin.
    apply in_map_iff in Hin as [integer_generator [Heq Hin]].
    subst generator. split.
    + apply project_group_solution_in_group.
    + apply (project_group_solution_constraints rows d matrix generators
        denominator integer_matrix Hpositive Hclear integer_generator).
      now apply Hgenerator_solution.
  - intro value. split.
    + intros [[coefficients Hcoefficients] Hconstraints].
      subst value.
      assert (Hpulled : HConicalConstraints
          (pulled_qmatrix matrix generators)
          (zvec_to_qvec coefficients)).
      { apply (proj2 (pulled_constraints_iff rows d matrix generators
          coefficients)). exact Hconstraints. }
      assert (Hinteger : forall row,
          0 <= zrow_qapply (Vector.nth integer_matrix row)
            (zvec_to_qvec coefficients)).
      { apply (proj1 (cleared_matrix_constraints_iff rows
          (length generators) (pulled_qmatrix matrix generators)
          denominator integer_matrix Hpositive Hclear
          (zvec_to_qvec coefficients))).
        exact Hpulled. }
      set (integer_solution :=
        Vector.append (zvec_positive coefficients)
          (Vector.append (zvec_negative coefficients)
            (integer_slack integer_matrix coefficients))).
      assert (Hsolution : HomogeneousSolution
          (homogenized_matrix integer_matrix) integer_solution).
      { unfold integer_solution.
        apply (cleared_point_homogeneous_solution rows (length generators)
          integer_matrix 1 coefficients (zvec_to_qvec coefficients)).
        - lia.
        - intro index. unfold qvec_scale, q_of_nat. cbn. ring.
        - exact Hinteger. }
      pose proof (proj1 (Hgenerated integer_solution) Hsolution) as
        [weights Hweights].
      pose proof (weighted_sum_project_group_generated rows d generators
        integer_generators weights integer_solution Hweights) as Hproject.
      unfold integer_solution in Hproject.
      rewrite project_group_integer_solution in Hproject.
      exact Hproject.
    + intro Hgenerated_value.
      apply (generated_in_periodic d
        (fun point : ZVec d =>
          ZGroupGenerated generators point /\
          HConicalConstraints matrix (zvec_to_qvec point))
        (List.map (@project_group_solution rows d generators)
          integer_generators) value).
      * apply group_hcone_intersection_periodic.
      * intros generator Hin.
        apply in_map_iff in Hin as [integer_generator [Heq Hin]].
        subst generator. split.
        -- apply project_group_solution_in_group.
        -- apply (project_group_solution_constraints rows d matrix generators
             denominator integer_matrix Hpositive Hclear integer_generator).
           now apply Hgenerator_solution.
      * exact Hgenerated_value.
Qed.
