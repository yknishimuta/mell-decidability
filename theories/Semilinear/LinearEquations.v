From Coq Require Import List Vector VectorSpec ZArith Lia
  Arith.Wf_nat Classical_Prop.
From KruskalAfProp Require Import af.af.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder Code.
From Mell.Order Require Import AlmostFullBridge CountableFiniteBasis.
From Mell.Semilinear Require Import Presentation.

Import ListNotations.

Definition ZMatrix (rows columns : nat) := Vector.t (ZVec columns) rows.

Fixpoint zrow_apply {d} (row : ZVec d) : NVec d -> Z :=
  match row with
  | @Vector.nil _ => fun _ => 0%Z
  | @Vector.cons _ coefficient tail_d tail => fun value =>
      (coefficient * Z.of_nat (Vector.hd value) +
        zrow_apply tail (Vector.tl value))%Z
  end.

Definition matrix_apply {rows d} (matrix : ZMatrix rows d)
    (value : NVec d) : ZVec rows :=
  Vector.map (fun row => zrow_apply row value) matrix.

Definition LinearSolution {rows d} (matrix : ZMatrix rows d)
    (constant : ZVec rows) (value : NVec d) : Prop :=
  matrix_apply matrix value = constant.

Definition HomogeneousSolution {rows d} (matrix : ZMatrix rows d)
    (value : NVec d) : Prop :=
  LinearSolution matrix (zvec_zero rows) value.

Definition nvec_sub {d} (upper lower : NVec d) : NVec d :=
  Vector.map2 Nat.sub upper lower.

Fixpoint nvec_weight {d} (value : NVec d) : nat :=
  match value with
  | @Vector.nil _ => 0
  | @Vector.cons _ head tail_d tail => head + nvec_weight tail
  end.

Definition GeneratedBy {d} (periods : list (NVec d)) (value : NVec d) : Prop :=
  exists coefficients, weighted_sum coefficients periods = Some value.

Lemma nvec_add_comm : forall d (left right : NVec d),
    nvec_add left right = nvec_add right left.
Proof.
  intros d left right. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma nvec_add_assoc_local : forall d (x y z : NVec d),
    nvec_add (nvec_add x y) z = nvec_add x (nvec_add y z).
Proof.
  intros d x y z. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma nvec_add_zero_left_local : forall d (value : NVec d),
    nvec_add (nvec_zero d) value = value.
Proof.
  intros d value. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add, nvec_zero.
  rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl),
    (const_nth nat 0 d index). lia.
Qed.

Lemma nvec_add_zero_right_local : forall d (value : NVec d),
    nvec_add value (nvec_zero d) = value.
Proof. intros; rewrite nvec_add_comm; apply nvec_add_zero_left_local. Qed.

Lemma nvec_scale_zero : forall d (value : NVec d),
    nvec_scale 0 value = nvec_zero d.
Proof.
  intros d value. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_scale, nvec_zero.
  rewrite (nth_map _ _ index index eq_refl), (const_nth nat 0 d index).
  lia.
Qed.

Lemma nvec_scale_one : forall d (value : NVec d), nvec_scale 1 value = value.
Proof.
  intros d value. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_scale.
  rewrite (nth_map _ _ index index eq_refl). lia.
Qed.

Lemma nvec_scale_add_coeff : forall d left right (value : NVec d),
    nvec_scale (left + right) value =
      nvec_add (nvec_scale left value) (nvec_scale right value).
Proof.
  intros d left right value.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_scale, nvec_add.
  repeat rewrite (nth_map _ _ index index eq_refl).
  rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  repeat rewrite (nth_map _ _ index index eq_refl). nia.
Qed.

Lemma nvec_sub_exact : forall d (lower upper : NVec d),
    nvec_le lower upper -> upper = nvec_add lower (nvec_sub upper lower).
Proof.
  intros d lower upper Hle.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add, nvec_sub.
  repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
  specialize (Hle index). lia.
Qed.

Lemma nvec_weight_zero : forall d, nvec_weight (nvec_zero d) = 0.
Proof.
  intro d. induction d as [|d IH]; cbn.
  - reflexivity.
  - exact IH.
Qed.

Lemma nvec_weight_eq_zero : forall d (value : NVec d),
    nvec_weight value = 0 -> value = nvec_zero d.
Proof.
  intros d value. induction value as [|head d tail IH]; intro Hweight.
  - reflexivity.
  - cbn in Hweight. assert (head = 0 /\ nvec_weight tail = 0) by lia.
    destruct H as [-> Htail]. rewrite (IH Htail). reflexivity.
Qed.

Lemma nvec_weight_positive : forall d (value : NVec d),
    value <> nvec_zero d -> 0 < nvec_weight value.
Proof.
  intros d value Hnonzero. destruct (nvec_weight value) eqn:Hweight; [|lia].
  exfalso. apply Hnonzero. now apply nvec_weight_eq_zero.
Qed.

Lemma nvec_weight_add : forall d (left right : NVec d),
    nvec_weight (nvec_add left right) = nvec_weight left + nvec_weight right.
Proof.
  intros d left. induction left as [|head d tail IH]; intro right.
  - refine (Vector.case0 (fun right =>
      nvec_weight (nvec_add (@Vector.nil nat) right) =
      nvec_weight (@Vector.nil nat) + nvec_weight right) _ right).
    reflexivity.
  - refine (Vector.caseS' right (fun right =>
      nvec_weight (nvec_add (@Vector.cons nat head d tail) right) =
      nvec_weight (@Vector.cons nat head d tail) + nvec_weight right) _).
    intros other rest. cbn. rewrite IH. lia.
Qed.

Lemma zrow_apply_zero : forall d (row : ZVec d),
    zrow_apply row (nvec_zero d) = 0%Z.
Proof.
  intros d row. unfold nvec_zero. induction row as [|coefficient d tail IH]; cbn.
  - reflexivity.
  - rewrite IH. ring.
Qed.

Lemma zrow_apply_add : forall d (row : ZVec d) (left right : NVec d),
    zrow_apply row (nvec_add left right) =
      (zrow_apply row left + zrow_apply row right)%Z.
Proof.
  intros d row. induction row as [|coefficient d tail IH]; intros left right.
  - reflexivity.
  - refine (Vector.caseS' left (fun left =>
      zrow_apply (@Vector.cons Z coefficient d tail) (nvec_add left right) =
      (zrow_apply (@Vector.cons Z coefficient d tail) left +
        zrow_apply (@Vector.cons Z coefficient d tail) right)%Z) _).
    intros left_head left_tail.
    refine (Vector.caseS' right (fun right =>
      zrow_apply (@Vector.cons Z coefficient d tail)
        (nvec_add (@Vector.cons nat left_head d left_tail) right) =
      (zrow_apply (@Vector.cons Z coefficient d tail)
          (@Vector.cons nat left_head d left_tail) +
        zrow_apply (@Vector.cons Z coefficient d tail) right)%Z) _).
    intros right_head right_tail. cbn. rewrite IH, Nat2Z.inj_add. ring.
Qed.

Lemma matrix_apply_zero : forall rows d (matrix : ZMatrix rows d),
    matrix_apply matrix (nvec_zero d) = zvec_zero rows.
Proof.
  intros rows d matrix. apply (proj1 (Vector.eq_nth_iff Z rows _ _)).
  intros index index' Heq; subst index'. unfold matrix_apply, zvec_zero.
  rewrite (nth_map _ _ index index eq_refl), (const_nth Z 0%Z rows index).
  apply zrow_apply_zero.
Qed.

Lemma matrix_apply_add : forall rows d (matrix : ZMatrix rows d) left right,
    matrix_apply matrix (nvec_add left right) =
      zvec_add (matrix_apply matrix left) (matrix_apply matrix right).
Proof.
  intros rows d matrix left right.
  apply (proj1 (Vector.eq_nth_iff Z rows _ _)).
  intros index index' Heq; subst index'. unfold matrix_apply, zvec_add.
  repeat rewrite (nth_map _ _ index index eq_refl).
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl).
  repeat rewrite (nth_map _ _ index index eq_refl).
  apply zrow_apply_add.
Qed.

Lemma linear_solution_dec : forall rows d (matrix : ZMatrix rows d)
    (constant : ZVec rows) value,
    {LinearSolution matrix constant value} +
    {~ LinearSolution matrix constant value}.
Proof.
  intros. unfold LinearSolution.
  apply Vector.eq_dec with (A_beq := Z.eqb). apply Z.eqb_eq.
Defined.

Definition enumerate_linear_solution {rows d} (matrix : ZMatrix rows d)
    (constant : ZVec rows) (nonzero : bool) (code : nat) : option (NVec d) :=
  match decode_nvec d code with
  | Some value =>
      if linear_solution_dec rows d matrix constant value then
        if nonzero then
          if nvec_eq_dec value (nvec_zero d) then None else Some value
        else Some value
      else None
  | None => None
  end.

Lemma enumerate_linear_solution_sound : forall rows d
    (matrix : ZMatrix rows d) constant nonzero code value,
    enumerate_linear_solution matrix constant nonzero code = Some value ->
    LinearSolution matrix constant value /\
      (nonzero = true -> value <> nvec_zero d).
Proof.
  intros rows d matrix constant nonzero code value Hdecode.
  unfold enumerate_linear_solution in Hdecode.
  destruct (decode_nvec d code) as [candidate|] eqn:Hcandidate;
    [|discriminate].
  destruct (linear_solution_dec rows d matrix constant candidate)
    as [Hsolution|Hsolution]; [|discriminate].
  destruct nonzero.
  - destruct (nvec_eq_dec candidate (nvec_zero d)) as [Heq|Hneq];
      inversion Hdecode; subst. auto.
  - inversion Hdecode; subst. split; [assumption|discriminate].
Qed.

Lemma enumerate_linear_solution_complete : forall rows d
    (matrix : ZMatrix rows d) constant nonzero value,
    LinearSolution matrix constant value ->
    (nonzero = true -> value <> nvec_zero d) ->
    exists code, enumerate_linear_solution matrix constant nonzero code = Some value.
Proof.
  intros rows d matrix constant nonzero value Hsolution Hnonzero.
  exists (encode_nvec value). unfold enumerate_linear_solution.
  rewrite decode_nvec_encode.
  destruct (linear_solution_dec rows d matrix constant value)
    as [_|Hcontra]; [|contradiction].
  destruct nonzero.
  - destruct (nvec_eq_dec value (nvec_zero d)) as [Heq|Hneq].
    + exfalso. apply (Hnonzero eq_refl). exact Heq.
    + reflexivity.
  - reflexivity.
Qed.

Lemma nvec_le_restricted_afs : forall d (P : NVec d -> Prop),
    afs P nvec_le.
Proof.
  intros d P. apply af_sub_rel_afs. apply af_af_sub_rel.
  apply nvec_le_almost_full.
Qed.

Theorem linear_solutions_finite_basis : forall rows d
    (matrix : ZMatrix rows d) (constant : ZVec rows),
    exists basis : list (NVec d),
      (forall base, List.In base basis -> LinearSolution matrix constant base) /\
      (forall value, LinearSolution matrix constant value ->
        exists base, List.In base basis /\ nvec_le base value).
Proof.
  intros rows d matrix constant.
  destruct (@countable_af_finite_cover (NVec d)
      (enumerate_linear_solution matrix constant false)
      (LinearSolution matrix constant) nvec_le nvec_le_dec)
    as [basis Hbasis].
  - intros code value Hdecode.
    now apply enumerate_linear_solution_sound in Hdecode.
  - intros value Hsolution.
    apply enumerate_linear_solution_complete; [exact Hsolution|discriminate].
  - apply nvec_le_restricted_afs.
  - exists (List.map (@proj1_sig _ _) basis). split.
    + intros base Hin. apply in_map_iff in Hin.
      destruct Hin as [[value Hvalid] [Heq _]]. cbn in Heq. subst base.
      exact Hvalid.
    + intros value Hsolution.
      destruct (Hbasis (exist _ value Hsolution)) as
        [[base Hbase] [Hin Hle]].
      exists base. split.
      * apply in_map_iff. exists (exist _ base Hbase). split; [reflexivity|exact Hin].
      * exact Hle.
Qed.

Lemma homogeneous_difference : forall rows d (matrix : ZMatrix rows d)
    lower upper,
    LinearSolution matrix (matrix_apply matrix lower) upper ->
    nvec_le lower upper ->
    HomogeneousSolution matrix (nvec_sub upper lower).
Proof.
  intros rows d matrix lower upper Hequal Hle.
  unfold LinearSolution in Hequal. cbn in Hequal.
  unfold HomogeneousSolution, LinearSolution.
  pose proof (nvec_sub_exact d lower upper Hle) as Hupper.
  rewrite Hupper, matrix_apply_add in Hequal.
  apply (proj1 (Vector.eq_nth_iff Z rows _ _)).
  intros index index' Hindex; subst index'.
  unfold zvec_zero.
  rewrite (const_nth Z 0%Z rows index).
  apply (f_equal (fun vector => Vector.nth vector index)) in Hequal.
  unfold zvec_add in Hequal.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl) in Hequal.
  lia.
Qed.

Lemma nvec_add_shuffle : forall d (a b c e : NVec d),
    nvec_add (nvec_add a b) (nvec_add c e) =
      nvec_add (nvec_add a c) (nvec_add b e).
Proof.
  intros d a b c e. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma weighted_sum_zero_coefficients : forall d (periods : list (NVec d)),
    weighted_sum (List.repeat 0 (List.length periods)) periods =
      Some (nvec_zero d).
Proof.
  intros d periods. induction periods as [|period periods IH]; cbn.
  - reflexivity.
  - rewrite IH, nvec_scale_zero, nvec_add_zero_left_local. reflexivity.
Qed.

Lemma weighted_sum_period : forall d (periods : list (NVec d)) period,
    List.In period periods ->
    exists coefficients, weighted_sum coefficients periods = Some period.
Proof.
  intros d periods. induction periods as [|head tail IH]; intros period Hin.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + exists (1 :: List.repeat 0 (List.length tail)). cbn.
      rewrite weighted_sum_zero_coefficients, nvec_scale_one,
        nvec_add_zero_right_local. reflexivity.
    + destruct (IH period Hin) as [coefficients Hcoefficients].
      exists (0 :: coefficients). cbn.
      rewrite Hcoefficients, nvec_scale_zero, nvec_add_zero_left_local.
      reflexivity.
Qed.

Lemma weighted_sum_add : forall d (periods : list (NVec d))
    left_coefficients right_coefficients left right,
    weighted_sum left_coefficients periods = Some left ->
    weighted_sum right_coefficients periods = Some right ->
    exists coefficients,
      weighted_sum coefficients periods = Some (nvec_add left right).
Proof.
  intros d periods. induction periods as [|period periods IH];
    intros left_coefficients right_coefficients left right Hleft Hright.
  - destruct left_coefficients; try discriminate.
    destruct right_coefficients; try discriminate.
    inversion Hleft; inversion Hright; subst.
    exists []. cbn. rewrite nvec_add_zero_left_local. reflexivity.
  - destruct left_coefficients as [|left_coefficient left_coefficients];
      try discriminate.
    destruct right_coefficients as [|right_coefficient right_coefficients];
      try discriminate.
    cbn in Hleft, Hright.
    destruct (weighted_sum left_coefficients periods) as [left_tail|]
      eqn:Hleft_tail; try discriminate.
    destruct (weighted_sum right_coefficients periods) as [right_tail|]
      eqn:Hright_tail; try discriminate.
    inversion Hleft; inversion Hright; subst left right.
    destruct (IH _ _ _ _ Hleft_tail Hright_tail) as
      [coefficients Hcoefficients].
    exists ((left_coefficient + right_coefficient) :: coefficients). cbn.
    rewrite Hcoefficients, nvec_scale_add_coeff, nvec_add_shuffle.
    reflexivity.
Qed.

Lemma generated_zero : forall d (periods : list (NVec d)),
    GeneratedBy periods (nvec_zero d).
Proof.
  intros. unfold GeneratedBy. exists (List.repeat 0 (List.length periods)).
  apply weighted_sum_zero_coefficients.
Qed.

Lemma generated_period : forall d (periods : list (NVec d)) period,
    List.In period periods -> GeneratedBy periods period.
Proof. intros; unfold GeneratedBy; now apply weighted_sum_period. Qed.

Lemma generated_add : forall d (periods : list (NVec d)) left right,
    GeneratedBy periods left -> GeneratedBy periods right ->
    GeneratedBy periods (nvec_add left right).
Proof.
  intros d periods left right [left_coefficients Hleft]
    [right_coefficients Hright]. unfold GeneratedBy.
  eapply weighted_sum_add; eauto.
Qed.

Lemma nvec_scale_succ : forall d coefficient (value : NVec d),
    nvec_scale (S coefficient) value =
      nvec_add value (nvec_scale coefficient value).
Proof.
  intros d coefficient value.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_scale, nvec_add.
  rewrite (nth_map _ _ index index eq_refl),
    (nth_map2 Nat.add _ _ index index index eq_refl eq_refl),
    (nth_map _ _ index index eq_refl). nia.
Qed.

Lemma homogeneous_zero : forall rows d (matrix : ZMatrix rows d),
    HomogeneousSolution matrix (nvec_zero d).
Proof. intros; unfold HomogeneousSolution, LinearSolution; apply matrix_apply_zero. Qed.

Lemma homogeneous_add : forall rows d (matrix : ZMatrix rows d) left right,
    HomogeneousSolution matrix left -> HomogeneousSolution matrix right ->
    HomogeneousSolution matrix (nvec_add left right).
Proof.
  intros rows d matrix left right Hleft Hright.
  unfold HomogeneousSolution, LinearSolution in *.
  rewrite matrix_apply_add, Hleft, Hright.
  apply (proj1 (Vector.eq_nth_iff Z rows _ _)).
  intros index index' Heq; subst index'. unfold zvec_add, zvec_zero.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    !const_nth. lia.
Qed.

Lemma homogeneous_scale : forall rows d (matrix : ZMatrix rows d)
    coefficient value,
    HomogeneousSolution matrix value ->
    HomogeneousSolution matrix (nvec_scale coefficient value).
Proof.
  intros rows d matrix coefficient. induction coefficient as [|coefficient IH];
    intros value Hvalue.
  - rewrite nvec_scale_zero. apply homogeneous_zero.
  - rewrite nvec_scale_succ. apply homogeneous_add; [exact Hvalue|].
    now apply IH.
Qed.

Lemma weighted_sum_homogeneous : forall rows d (matrix : ZMatrix rows d)
    periods coefficients value,
    (forall period, List.In period periods -> HomogeneousSolution matrix period) ->
    weighted_sum coefficients periods = Some value ->
    HomogeneousSolution matrix value.
Proof.
  intros rows d matrix periods. induction periods as [|period periods IH];
    intros coefficients value Hperiods Hsum.
  - destruct coefficients; cbn in Hsum; try discriminate.
    inversion Hsum; subst. apply homogeneous_zero.
  - destruct coefficients as [|coefficient coefficients]; try discriminate.
    cbn in Hsum.
    destruct (weighted_sum coefficients periods) as [tail|] eqn:Htail;
      try discriminate.
    inversion Hsum; subst value. apply homogeneous_add.
    + apply homogeneous_scale. apply Hperiods. now left.
    + eapply IH; [|exact Htail]. intros tail_period Hin.
      apply Hperiods. now right.
Qed.

Lemma homogeneous_nonzero_finite_basis : forall rows d
    (matrix : ZMatrix rows d),
    exists basis : list (NVec d),
      (forall base, List.In base basis ->
        HomogeneousSolution matrix base /\ base <> nvec_zero d) /\
      (forall value, HomogeneousSolution matrix value ->
        value <> nvec_zero d ->
        exists base, List.In base basis /\ nvec_le base value).
Proof.
  intros rows d matrix.
  destruct (@countable_af_finite_cover (NVec d)
      (enumerate_linear_solution matrix (zvec_zero rows) true)
      (fun value => HomogeneousSolution matrix value /\ value <> nvec_zero d)
      nvec_le nvec_le_dec) as [basis Hbasis].
  - intros code value Hdecode.
    apply enumerate_linear_solution_sound in Hdecode.
    destruct Hdecode as [Hsolution Hnonzero]. split; [exact Hsolution|auto].
  - intros value [Hsolution Hnonzero].
    apply enumerate_linear_solution_complete; [exact Hsolution|auto].
  - apply nvec_le_restricted_afs.
  - exists (List.map (@proj1_sig _ _) basis). split.
    + intros base Hin. apply in_map_iff in Hin.
      destruct Hin as [[value Hvalid] [Heq _]]. cbn in Heq. subst base.
      exact Hvalid.
    + intros value Hsolution Hnonzero.
      destruct (Hbasis (exist _ value (conj Hsolution Hnonzero))) as
        [[base [Hbase Hbase_nonzero]] [Hin Hle]].
      exists base. split.
      * apply in_map_iff. exists (exist _ base (conj Hbase Hbase_nonzero)).
        split; [reflexivity|exact Hin].
      * exact Hle.
Qed.

Theorem homogeneous_solutions_finitely_generated : forall rows d
    (matrix : ZMatrix rows d),
    exists generators : list (NVec d),
      (forall generator, List.In generator generators ->
        HomogeneousSolution matrix generator) /\
      (forall value, HomogeneousSolution matrix value <->
        GeneratedBy generators value).
Proof.
  intros rows d matrix.
  destruct (homogeneous_nonzero_finite_basis rows d matrix) as
    [generators [Hgenerators Hcover]].
  exists generators. split.
  - intros generator Hin. exact (proj1 (Hgenerators generator Hin)).
  - intro value. split.
    + intro Hhomogeneous.
      assert (Hbounded : forall bound candidate,
          nvec_weight candidate < bound ->
          HomogeneousSolution matrix candidate ->
          GeneratedBy generators candidate).
      { intro bound. induction bound as [|bound IH];
          intros candidate Hweight Hcandidate; [lia|].
        destruct (nvec_eq_dec candidate (nvec_zero d)) as [->|Hnonzero].
        - apply generated_zero.
        - destruct (Hcover candidate Hcandidate Hnonzero) as
            [generator [Hin Hle]].
          set (remainder := nvec_sub candidate generator).
          assert (Hgenerator := proj1 (Hgenerators generator Hin)).
          assert (Hcandidate_eq :
              candidate = nvec_add generator remainder).
          { unfold remainder. apply nvec_sub_exact. exact Hle. }
          assert (Hremainder : HomogeneousSolution matrix remainder).
          { unfold remainder. eapply homogeneous_difference; [|exact Hle].
            unfold LinearSolution. rewrite Hcandidate, Hgenerator. reflexivity. }
          assert (Hremainder_weight : nvec_weight remainder < bound).
          { rewrite Hcandidate_eq, nvec_weight_add in Hweight.
            pose proof (nvec_weight_positive d generator
              (proj2 (Hgenerators generator Hin))). lia. }
          rewrite Hcandidate_eq. apply generated_add.
          + now apply generated_period.
          + apply IH; assumption. }
      apply (Hbounded (S (nvec_weight value)) value); [lia|exact Hhomogeneous].
    + intros [coefficients Hcoefficients].
      eapply weighted_sum_homogeneous; [|exact Hcoefficients].
      intros period Hin. exact (proj1 (Hgenerators period Hin)).
Qed.

Theorem linear_solution_decomposition : forall rows d
    (matrix : ZMatrix rows d) (constant : ZVec rows),
    exists basis : list (NVec d),
      (forall base, List.In base basis -> LinearSolution matrix constant base) /\
      (forall value, LinearSolution matrix constant value ->
        exists base homogeneous,
          List.In base basis /\
          HomogeneousSolution matrix homogeneous /\
          value = nvec_add base homogeneous).
Proof.
  intros rows d matrix constant.
  destruct (linear_solutions_finite_basis rows d matrix constant) as
    [basis [Hbasis Hcover]].
  exists basis. split; [exact Hbasis|].
  intros value Hsolution.
  destruct (Hcover value Hsolution) as [base [Hin Hle]].
  exists base, (nvec_sub value base). repeat split; try assumption.
  - eapply homogeneous_difference; [|exact Hle].
    unfold LinearSolution. rewrite Hsolution, (Hbasis base Hin). reflexivity.
  - apply nvec_sub_exact. exact Hle.
Qed.

Lemma zvec_add_zero_right_local : forall d (value : ZVec d),
    zvec_add value (zvec_zero d) = value.
Proof.
  intros d value. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'. unfold zvec_add, zvec_zero.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    const_nth. lia.
Qed.

Theorem linear_equations_semicode : forall rows d
    (matrix : ZMatrix rows d) (constant : ZVec rows),
    exists code : SemiCode d,
      forall value, LinearSolution matrix constant value <-> denote code value.
Proof.
  intros rows d matrix constant.
  destruct (homogeneous_solutions_finitely_generated rows d matrix) as
    [generators [Hgenerators Hgenerated]].
  destruct (linear_solution_decomposition rows d matrix constant) as
    [basis [Hbasis Hdecompose]].
  exists (List.map (fun base => (base, generators)) basis). intro value.
  split.
  - intro Hsolution.
    destruct (Hdecompose value Hsolution) as
      [base [homogeneous [Hin [Hhomogeneous Hvalue]]]].
    destruct (proj1 (Hgenerated homogeneous) Hhomogeneous) as
      [coefficients Hcoefficients].
    exists (base, generators). split.
    + apply in_map_iff. exists base. split; [reflexivity|exact Hin].
    + exists coefficients, homogeneous. split; [exact Hcoefficients|].
      exact Hvalue.
  - intros [[base periods] [Hin [coefficients [contribution
      [Hcoefficients Hvalue]]]]].
    apply in_map_iff in Hin.
    destruct Hin as [basis_value [Heq Hin]].
    destruct Heq.
    specialize (Hbasis basis_value Hin).
    assert (Hhomogeneous : HomogeneousSolution matrix contribution).
    { apply (proj2 (Hgenerated contribution)).
      exists coefficients. exact Hcoefficients. }
    unfold LinearSolution in Hbasis |- *.
    unfold HomogeneousSolution, LinearSolution in Hhomogeneous.
    rewrite Hvalue, matrix_apply_add.
    transitivity (zvec_add constant (zvec_zero rows)).
    + f_equal; assumption.
    + apply zvec_add_zero_right_local.
Qed.
