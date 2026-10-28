From Coq Require Import Fin Lia List Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import FaceStrippingExtract LatticeGordanH
  LatticeGordanInterface LatticeGordanMain LatticeGordanPullback
  MathCompBridge Periodic QConeCore RationalDefinability RationalHToV.
From Mell.Semilinear Require Import LinearEquations.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.

Fixpoint zinner {d} (normal : ZVec d) : ZVec d -> Z :=
  match normal with
  | @Vector.nil _ => fun _ => 0
  | @Vector.cons _ coefficient tail_d tail => fun value =>
      coefficient * Vector.hd value + zinner tail (Vector.tl value)
  end.

Lemma zinner_zero : forall d (normal : ZVec d),
    zinner normal (zvec_zero d) = 0.
Proof.
  intros d normal. unfold zvec_zero.
  induction normal as [|coefficient d tail IH]; cbn.
  - reflexivity.
  - rewrite IH. ring.
Qed.

Lemma zinner_add : forall d (normal left right : ZVec d),
    zinner normal (zvec_add left right) =
      zinner normal left + zinner normal right.
Proof.
  intros d normal. induction normal as [|coefficient d tail IH];
    intros left right.
  - reflexivity.
  - revert right. refine (Vector.caseS' left (fun left => forall right,
      zinner (@Vector.cons Z coefficient d tail) (zvec_add left right) =
        zinner (@Vector.cons Z coefficient d tail) left +
          zinner (@Vector.cons Z coefficient d tail) right) _).
    intros left_head left_tail right.
    refine (Vector.caseS' right (fun right =>
      zinner (@Vector.cons Z coefficient d tail)
          (zvec_add (@Vector.cons Z left_head d left_tail) right) =
        zinner (@Vector.cons Z coefficient d tail)
            (@Vector.cons Z left_head d left_tail) +
          zinner (@Vector.cons Z coefficient d tail) right) _).
    intros right_head right_tail. cbn. rewrite IH. ring.
Qed.

Lemma zinner_zsmul : forall d coefficient (normal value : ZVec d),
    zinner normal (zvec_zsmul coefficient value) =
      coefficient * zinner normal value.
Proof.
  intros d coefficient normal. induction normal as [|head d tail IH];
    intro value.
  - refine (Vector.case0 (fun value =>
      zinner (@Vector.nil Z) (zvec_zsmul coefficient value) =
        coefficient * zinner (@Vector.nil Z) value) _ value).
    cbn [zvec_zsmul zinner Vector.map]. ring.
  - refine (Vector.caseS' value (fun value =>
      zinner (@Vector.cons Z head d tail) (zvec_zsmul coefficient value) =
        coefficient * zinner (@Vector.cons Z head d tail) value) _).
    intros value_head value_tail.
    cbn [zvec_zsmul zinner Vector.map].
    specialize (IH value_tail). unfold zvec_zsmul in IH.
    change (head * (coefficient * value_head) +
      zinner tail (Vector.map (Z.mul coefficient) value_tail) =
      coefficient * (head * value_head + zinner tail value_tail)).
    rewrite IH. ring.
Qed.

Lemma zinner_positive_negative : forall d (normal value : ZVec d),
    zinner normal value =
      zrow_apply normal (zvec_positive value) -
        zrow_apply normal (zvec_negative value).
Proof.
  intros d normal. induction normal as [|coefficient d tail IH]; intro value.
  - reflexivity.
  - refine (Vector.caseS' value (fun value =>
      zinner (@Vector.cons Z coefficient d tail) value =
        zrow_apply (@Vector.cons Z coefficient d tail) (zvec_positive value) -
          zrow_apply (@Vector.cons Z coefficient d tail)
            (zvec_negative value)) _).
    intros value_head value_tail.
    unfold zvec_positive, zvec_negative in IH |- *.
    cbn [zinner zrow_apply Vector.map].
    change (coefficient * value_head + zinner tail value_tail =
      coefficient * Z.of_nat (Z.to_nat value_head) +
        zrow_apply tail (Vector.map Z.to_nat value_tail) -
      (coefficient * Z.of_nat (Z.to_nat (- value_head)) +
        zrow_apply tail
          (Vector.map (fun coordinate => Z.to_nat (- coordinate))
            value_tail))).
    rewrite IH.
    assert (Hhead : value_head =
        Z.of_nat (Z.to_nat value_head) -
          Z.of_nat (Z.to_nat (- value_head))).
    { rewrite !ZifyInst.of_nat_to_nat_eq. lia. }
    replace (coefficient * value_head) with
      (coefficient * (Z.of_nat (Z.to_nat value_head) -
        Z.of_nat (Z.to_nat (- value_head)))) by (f_equal; symmetry; exact Hhead).
    ring.
Qed.

Definition AffineSolutions {d}
    (constraints : list (ZVec d * Z)) : ZSet d :=
  fun value => forall constraint,
    List.In constraint constraints ->
    (snd constraint <= zinner (fst constraint) value)%Z.

Definition HomogeneousSolutions {d}
    (constraints : list (ZVec d * Z)) : ZSet d :=
  fun value => forall constraint,
    List.In constraint constraints ->
    (0 <= zinner (fst constraint) value)%Z.

Definition constraint_vector {d} (constraints : list (ZVec d * Z)) :=
  Vector.of_list constraints.

Definition constraint_matrix {d} (constraints : list (ZVec d * Z)) :
    ZMatrix (length constraints) d :=
  Vector.map fst (constraint_vector constraints).

Definition constraint_constant {d} (constraints : list (ZVec d * Z)) :
    ZVec (length constraints) :=
  Vector.map snd (constraint_vector constraints).

Lemma constraint_matrix_nth : forall d constraints
    (row : Fin.t (length constraints)),
    Vector.nth (constraint_matrix (d := d) constraints) row =
      fst (Vector.nth (constraint_vector constraints) row).
Proof.
  intros. unfold constraint_matrix.
  rewrite (nth_map _ _ row row eq_refl). reflexivity.
Qed.

Lemma constraint_constant_nth : forall d constraints
    (row : Fin.t (length constraints)),
    Vector.nth (constraint_constant (d := d) constraints) row =
      snd (Vector.nth (constraint_vector constraints) row).
Proof.
  intros. unfold constraint_constant.
  rewrite (nth_map _ _ row row eq_refl). reflexivity.
Qed.

Lemma vector_of_list_forall_iff : forall (A : Type) (property : A -> Prop)
    (values : list A),
    (forall index, property (Vector.nth (Vector.of_list values) index)) <->
    List.Forall property values.
Proof.
  intros A property values. induction values as [|value values IH].
  - split.
    + intro H. constructor.
    + intros H index. inversion index.
  - split.
    + intro H. constructor.
      * exact (H Fin.F1).
      * apply (proj1 IH). intro index. exact (H (Fin.FS index)).
    + intro H. inversion H as [|value' values' Hvalue Hvalues]; subst.
      intro index. refine (Fin.caseS' index (fun index =>
        property (Vector.nth (Vector.of_list (value :: values)) index)) _ _).
      * exact Hvalue.
      * intro tail_index. apply (proj2 IH Hvalues tail_index).
Qed.

Lemma affine_solutions_rows : forall d constraints (value : ZVec d),
    AffineSolutions constraints value <->
    forall row : Fin.t (length constraints),
      (Vector.nth (constraint_constant (d := d) constraints) row <=
       zinner (Vector.nth (constraint_matrix constraints) row) value)%Z.
Proof.
  intros d constraints value.
  unfold AffineSolutions. rewrite <- List.Forall_forall.
  rewrite <- (vector_of_list_forall_iff (ZVec d * Z)
    (fun constraint => (snd constraint <= zinner (fst constraint) value)%Z)
    constraints).
  split.
  - intros H row. specialize (H row).
    rewrite (constraint_constant_nth d constraints row),
      (constraint_matrix_nth d constraints row).
    exact H.
  - intros H row. specialize (H row).
    rewrite (constraint_constant_nth d constraints row),
      (constraint_matrix_nth d constraints row) in H.
    exact H.
Qed.

Lemma homogeneous_solutions_rows : forall d constraints (value : ZVec d),
    HomogeneousSolutions constraints value <->
    forall row : Fin.t (length constraints),
      (0 <= zinner (Vector.nth (constraint_matrix constraints) row) value)%Z.
Proof.
  intros d constraints value.
  unfold HomogeneousSolutions. rewrite <- List.Forall_forall.
  rewrite <- (vector_of_list_forall_iff (ZVec d * Z)
    (fun constraint => (0 <= zinner (fst constraint) value)%Z)
    constraints).
  split.
  - intros H row. specialize (H row).
    rewrite (constraint_matrix_nth d constraints row). exact H.
  - intros H row. specialize (H row).
    rewrite (constraint_matrix_nth d constraints row) in H. exact H.
Qed.

Lemma affine_homogenized_solution_exact : forall rows d
    (matrix : ZMatrix rows d) (constant : ZVec rows)
    (positive negative : NVec d) (slack : NVec rows),
    LinearSolution (homogenized_matrix matrix) constant
      (Vector.append positive (Vector.append negative slack)) <->
    forall row,
      (zrow_apply (Vector.nth matrix row) positive -
        zrow_apply (Vector.nth matrix row) negative -
        Z.of_nat (Vector.nth slack row) = Vector.nth constant row)%Z.
Proof.
  intros rows d matrix constant positive negative slack.
  unfold LinearSolution, matrix_apply. split.
  - intros Heq row.
    pose proof ((proj2 (Vector.eq_nth_iff Z rows _ _) Heq)
      row row eq_refl) as Hrow.
    rewrite (nth_map _ _ row row eq_refl), homogenized_matrix_nth,
      zrow_apply_homogenized in Hrow. exact Hrow.
  - intro Hrows. apply (proj1 (Vector.eq_nth_iff Z rows _ _)).
    intros row row' Heq; subst row'.
    rewrite (nth_map _ _ row row eq_refl), homogenized_matrix_nth,
      zrow_apply_homogenized.
    apply Hrows.
Qed.

Lemma zinner_nvec_difference : forall d (normal : ZVec d)
    (positive negative : NVec d),
    zinner normal
      (Vector.map2 (fun p n => (Z.of_nat p - Z.of_nat n)%Z)
        positive negative) =
      (zrow_apply normal positive - zrow_apply normal negative)%Z.
Proof.
  intros d normal. induction normal as [|coefficient d tail IH];
    intros positive negative.
  - refine (Vector.case0 (fun positive => forall negative : NVec 0,
      zinner (@Vector.nil Z)
          (Vector.map2 (fun p n => Z.of_nat p - Z.of_nat n)
            positive negative) =
        zrow_apply (@Vector.nil Z) positive -
          zrow_apply (@Vector.nil Z) negative) _ positive negative).
    intro negative'. refine (Vector.case0 (fun negative => _) _ negative').
    reflexivity.
  - revert negative. refine (Vector.caseS' positive (fun positive =>
      forall negative : NVec (S d),
        zinner (@Vector.cons Z coefficient d tail)
            (Vector.map2 (fun p n => Z.of_nat p - Z.of_nat n)
              positive negative) =
          zrow_apply (@Vector.cons Z coefficient d tail) positive -
            zrow_apply (@Vector.cons Z coefficient d tail) negative) _).
    intros positive_head positive_tail negative.
    refine (Vector.caseS' negative (fun negative =>
      zinner (@Vector.cons Z coefficient d tail)
          (Vector.map2 (fun p n => Z.of_nat p - Z.of_nat n)
            (@Vector.cons nat positive_head d positive_tail) negative) =
        zrow_apply (@Vector.cons Z coefficient d tail)
            (@Vector.cons nat positive_head d positive_tail) -
          zrow_apply (@Vector.cons Z coefficient d tail) negative) _).
    intros negative_head negative_tail. cbn. rewrite IH. ring.
Qed.

Lemma zinner_solution_coefficients : forall rows d (normal : ZVec d)
    (value : NVec (d + (d + rows))),
    zinner normal (solution_coefficients value) =
      (zrow_apply normal (solution_positive value) -
        zrow_apply normal (solution_negative value))%Z.
Proof. intros. unfold solution_coefficients. apply zinner_nvec_difference. Qed.

Lemma linear_solution_projects_affine : forall d constraints
    (value : NVec (d + (d + length constraints))),
    LinearSolution (homogenized_matrix (constraint_matrix constraints))
      (constraint_constant constraints) value ->
    AffineSolutions constraints (solution_coefficients value).
Proof.
  intros d constraints value Hsolution.
  apply (proj2 (affine_solutions_rows d constraints _)). intro row.
  pose proof (solution_three_parts (length constraints) d value) as Hparts.
  rewrite Hparts in Hsolution.
  pose proof (proj1 (affine_homogenized_solution_exact
    (length constraints) d (constraint_matrix constraints)
    (constraint_constant constraints) _ _ _) Hsolution row) as Hrow.
  rewrite zinner_solution_coefficients. lia.
Qed.

Lemma homogeneous_solution_projects : forall d constraints
    (value : NVec (d + (d + length constraints))),
    HomogeneousSolution (homogenized_matrix (constraint_matrix constraints))
      value ->
    HomogeneousSolutions constraints (solution_coefficients value).
Proof.
  intros d constraints value Hsolution.
  apply (proj2 (homogeneous_solutions_rows d constraints _)). intro row.
  pose proof (solution_three_parts (length constraints) d value) as Hparts.
  rewrite Hparts in Hsolution.
  pose proof (proj1 (@homogenized_solution_exact (length constraints) d
    (constraint_matrix constraints) _ _ _) Hsolution row) as Hrow.
  rewrite zinner_solution_coefficients, Hrow. lia.
Qed.

Definition affine_slack {d} (constraints : list (ZVec d * Z))
    (value : ZVec d) : NVec (length constraints) :=
  vector_of_finfun nat (length constraints) (fun row => Z.to_nat
    (zinner (Vector.nth (constraint_matrix constraints) row) value -
      Vector.nth (constraint_constant constraints) row)).

Lemma affine_slack_nth : forall d constraints (value : ZVec d) row,
    Vector.nth (affine_slack constraints value) row = Z.to_nat
      (zinner (Vector.nth (constraint_matrix constraints) row) value -
        Vector.nth (constraint_constant constraints) row).
Proof. intros. unfold affine_slack. apply vector_of_finfun_nth. Qed.

Lemma affine_solution_lift : forall d constraints (value : ZVec d),
    AffineSolutions constraints value ->
    LinearSolution (homogenized_matrix (constraint_matrix constraints))
      (constraint_constant constraints)
      (Vector.append (zvec_positive value)
        (Vector.append (zvec_negative value) (affine_slack constraints value))).
Proof.
  intros d constraints value Haffine.
  apply (proj2 (affine_homogenized_solution_exact
    (length constraints) d (constraint_matrix constraints)
    (constraint_constant constraints) _ _ _)). intro row.
  rewrite affine_slack_nth.
  pose proof (proj1 (affine_solutions_rows d constraints value)
    Haffine row) as Hrow.
  rewrite <- zinner_positive_negative in *.
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma solution_coefficients_lift : forall rows d (value : ZVec d)
    (slack : NVec rows),
    solution_coefficients
      (Vector.append (zvec_positive value)
        (Vector.append (zvec_negative value) slack)) = value.
Proof.
  intros rows d value slack. apply zvec_ext. intro index.
  rewrite solution_coefficients_append. apply zvec_positive_negative.
Qed.

Lemma affine_solutions_add_homogeneous : forall d constraints
    (base increment : ZVec d),
    AffineSolutions constraints base ->
    HomogeneousSolutions constraints increment ->
    AffineSolutions constraints (zvec_add base increment).
Proof.
  intros d constraints base increment Hbase Hincrement constraint Hin.
  rewrite zinner_add. specialize (Hbase constraint Hin).
  specialize (Hincrement constraint Hin). lia.
Qed.

Lemma homogeneous_solutions_periodic : forall d constraints,
    Periodic (@HomogeneousSolutions d constraints).
Proof.
  intros d constraints. split.
  - intros constraint Hin. rewrite zinner_zero. lia.
  - intros left right Hleft Hright constraint Hin.
    rewrite zinner_add. specialize (Hleft constraint Hin).
    specialize (Hright constraint Hin). lia.
Qed.

Theorem integer_affine_inequalities_finitary : forall d constraints,
    exists bases : list (ZVec d),
      List.Forall (AffineSolutions constraints) bases /\
      SameSet
        (AffineSolutions constraints)
        (fun value => exists base homogeneous,
          List.In base bases /\
          HomogeneousSolutions constraints homogeneous /\
          value = zvec_add base homogeneous).
Proof.
  intros d constraints.
  destruct (linear_solution_decomposition (length constraints)
    (d + (d + length constraints))
    (homogenized_matrix (constraint_matrix constraints))
    (constraint_constant constraints)) as [raw_bases [Hraw Hdecompose]].
  set (bases := List.map (@solution_coefficients (length constraints) d)
    raw_bases).
  assert (Hbases : List.Forall (AffineSolutions constraints) bases).
  { apply List.Forall_forall. intros base Hin.
    apply in_map_iff in Hin as [raw_base [Heq Hin]]. subst base.
    apply linear_solution_projects_affine. now apply Hraw. }
  exists bases. split; [exact Hbases|]. intro value. split.
  - intro Hvalue.
    set (lifted := Vector.append (zvec_positive value)
      (Vector.append (zvec_negative value) (affine_slack constraints value))).
    assert (Hlifted : LinearSolution
        (homogenized_matrix (constraint_matrix constraints))
        (constraint_constant constraints) lifted).
    { unfold lifted. now apply affine_solution_lift. }
    destruct (Hdecompose lifted Hlifted) as
      [raw_base [raw_homogeneous [Hin [Hhomogeneous Heq]]]].
    exists (solution_coefficients raw_base),
      (solution_coefficients raw_homogeneous). repeat split.
    + unfold bases. apply in_map. exact Hin.
    + now apply homogeneous_solution_projects.
    + rewrite <- (solution_coefficients_lift (length constraints) d value
        (affine_slack constraints value)).
      unfold lifted in Heq. rewrite Heq, solution_coefficients_add.
      reflexivity.
  - intros [base [homogeneous [Hin [Hhomogeneous ->]]]].
    apply affine_solutions_add_homogeneous.
    + apply (proj1 (List.Forall_forall _ _ ) Hbases base Hin).
    + exact Hhomogeneous.
Qed.

Definition AffineGroupSolutions {d} (group : ZSet d)
    (constraints : list (ZVec d * Z)) : ZSet d :=
  fun value => group value /\ AffineSolutions constraints value.

Definition HomogeneousGroupSolutions {d} (group : ZSet d)
    (constraints : list (ZVec d * Z)) : ZSet d :=
  fun value => group value /\ HomogeneousSolutions constraints value.

Fixpoint pull_integer_normal {d} (normal : ZVec d)
    (generators : list (ZVec d)) : ZVec (length generators) :=
  match generators with
  | [] => @Vector.nil Z
  | generator :: generators' =>
      @Vector.cons Z (zinner normal generator) (length generators')
        (pull_integer_normal normal generators')
  end.

Lemma zinner_pull_integer_normal : forall d (normal : ZVec d)
    (generators : list (ZVec d)) coefficients,
    zinner (pull_integer_normal normal generators) coefficients =
      zinner normal (F_Z generators coefficients).
Proof.
  intros d normal generators. induction generators as
      [|generator generators IH]; intro coefficients.
  - refine (Vector.case0 (fun coefficients =>
      zinner (pull_integer_normal normal []) coefficients =
        zinner normal (F_Z [] coefficients)) _ coefficients).
    unfold F_Z. cbn [pull_integer_normal zgroup_combination].
    change (0 = zinner normal (zvec_zero d)). symmetry. apply zinner_zero.
  - refine (Vector.caseS' coefficients (fun coefficients =>
      zinner (pull_integer_normal normal (generator :: generators))
          coefficients =
        zinner normal (F_Z (generator :: generators) coefficients)) _).
    intros head tail.
    change (zinner normal generator * head +
        zinner (pull_integer_normal normal generators) tail =
      zinner normal
        (zvec_add (zvec_zsmul head generator) (F_Z generators tail))).
    rewrite zinner_add, zinner_zsmul, IH. ring.
Qed.

Definition pull_integer_constraints {d} (generators : list (ZVec d))
    (constraints : list (ZVec d * Z)) :
    list (ZVec (length generators) * Z) :=
  List.map (fun constraint =>
    (pull_integer_normal (fst constraint) generators, snd constraint))
    constraints.

Lemma affine_solutions_pull_iff : forall d (generators : list (ZVec d))
    constraints coefficients,
    AffineSolutions (pull_integer_constraints generators constraints)
      coefficients <->
    AffineSolutions constraints (F_Z generators coefficients).
Proof.
  intros d generators constraints coefficients. split.
  - intros H constraint Hin.
    assert (Hmapped : List.In
      (pull_integer_normal (fst constraint) generators, snd constraint)
      (pull_integer_constraints generators constraints)).
    { apply (in_map (fun constraint =>
      (pull_integer_normal (fst constraint) generators, snd constraint))
      constraints constraint Hin). }
    specialize (H _ Hmapped) as Hconstraint.
    cbn in Hconstraint. now rewrite zinner_pull_integer_normal in Hconstraint.
  - intros H pulled_constraint Hin.
    apply in_map_iff in Hin as [constraint [Heq Hin]]. subst pulled_constraint.
    cbn. rewrite zinner_pull_integer_normal. now apply H.
Qed.

Lemma homogeneous_solutions_pull_iff : forall d
    (generators : list (ZVec d)) constraints coefficients,
    HomogeneousSolutions (pull_integer_constraints generators constraints)
      coefficients <->
    HomogeneousSolutions constraints (F_Z generators coefficients).
Proof.
  intros d generators constraints coefficients. split.
  - intros H constraint Hin.
    assert (Hmapped : List.In
      (pull_integer_normal (fst constraint) generators, snd constraint)
      (pull_integer_constraints generators constraints)).
    { apply (in_map (fun constraint =>
      (pull_integer_normal (fst constraint) generators, snd constraint))
      constraints constraint Hin). }
    specialize (H _ Hmapped) as Hconstraint.
    cbn in Hconstraint. now rewrite zinner_pull_integer_normal in Hconstraint.
  - intros H pulled_constraint Hin.
    apply in_map_iff in Hin as [constraint [Heq Hin]]. subst pulled_constraint.
    cbn. rewrite zinner_pull_integer_normal. now apply H.
Qed.

Lemma homogeneous_group_solutions_periodic : forall d (group : ZSet d)
    constraints,
    FinitelyGeneratedGroup group ->
    Periodic (HomogeneousGroupSolutions group constraints).
Proof.
  intros d group constraints Hgroup.
  destruct (finitely_generated_group_periodic d group Hgroup)
    as [Hgroup_zero Hgroup_add].
  destruct (homogeneous_solutions_periodic d constraints)
    as [Hconstraints_zero Hconstraints_add].
  split.
  - split; assumption.
  - intros left right [Hleft_group Hleft_constraints]
      [Hright_group Hright_constraints]. split.
    + now apply Hgroup_add.
    + now apply Hconstraints_add.
Qed.

Theorem affine_group_inequalities_finitary : forall d (group : ZSet d)
    constraints,
    FinitelyGeneratedGroup group ->
    FinitaryQCylindric
      (HomogeneousGroupSolutions group constraints)
      (AffineGroupSolutions group constraints).
Proof.
  intros d group constraints [generators Hgroup].
  destruct (integer_affine_inequalities_finitary (length generators)
    (pull_integer_constraints generators constraints)) as
    [coefficient_bases [Hcoefficient_bases Hcoefficient_cover]].
  set (bases := List.map (F_Z generators) coefficient_bases).
  exists bases. intro value. split.
  - intros [Hvalue_group Hvalue_affine].
    apply (proj1 (Hgroup value)) in Hvalue_group.
    destruct Hvalue_group as [coefficients Hcoefficients].
    change (F_Z generators coefficients = value) in Hcoefficients.
    subst value.
    apply (proj2 (affine_solutions_pull_iff d generators constraints
      coefficients)) in Hvalue_affine.
    destruct (proj1 (Hcoefficient_cover coefficients) Hvalue_affine) as
      [base [homogeneous [Hin [Hhomogeneous Heq]]]].
    exists (F_Z generators base), (F_Z generators homogeneous).
    repeat split.
    + unfold bases. apply in_map. exact Hin.
    + apply (proj2 (Hgroup _)). exists homogeneous. reflexivity.
    + apply (proj1 (homogeneous_solutions_pull_iff d generators constraints
        homogeneous)). exact Hhomogeneous.
    + rewrite <- F_Z_add, <- Heq. reflexivity.
  - intros [base [increment [Hin [[Hincrement_group
        Hincrement_constraints] Heq]]]].
    apply in_map_iff in Hin as [coefficient_base [Hbase_eq Hbase_in]].
    subst base. subst value. split.
    + destruct (finitely_generated_group_periodic d group
        ltac:(exists generators; exact Hgroup)) as [_ Hgroup_add].
      apply Hgroup_add; [|exact Hincrement_group].
      apply (proj2 (Hgroup _)). exists coefficient_base. reflexivity.
    + apply affine_solutions_add_homogeneous; [|exact Hincrement_constraints].
      apply (proj1 (affine_solutions_pull_iff d generators constraints
        coefficient_base)).
      apply (proj1 (List.Forall_forall _ _)
        Hcoefficient_bases coefficient_base Hbase_in).
Qed.
