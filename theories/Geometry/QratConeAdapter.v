From Coq Require Import List QArith Permutation.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From Polyhedra Require Import polyhedron barycenter.
From Mell.Geometry Require Import MathCompBridge QConeCore LatticeGordanV
  QratAdapter QratVectorAdapter.

Import GRing.Theory Num.Theory Order.Theory.
Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Definition rat_fset_of_columns {d}
    (columns : list ('cV[rat]_d)) : {fset 'cV[rat]_d} :=
  [fset column in columns]%fset.

Definition rat_fset_of_generators {d}
    (generators : list (QVec d)) : {fset 'cV[rat]_d} :=
  rat_fset_of_columns (rat_cols_of_list generators).

Lemma rat_fset_of_generators_member : forall d
    (generators : list (QVec d)) (generator : QVec d),
    List.In generator generators ->
    qvec_to_rat_col generator \in rat_fset_of_generators generators.
Proof.
  intros d generators. induction generators as [|head tail IH];
    intros generator Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [<- | Hin].
    + rewrite /rat_fset_of_generators /rat_fset_of_columns
        /rat_cols_of_list /= in_fset_cons eqxx.
      reflexivity.
    + rewrite /rat_fset_of_generators /rat_fset_of_columns
        /rat_cols_of_list /= in_fset_cons.
      apply/orP. right. apply IH. exact Hin.
Qed.

Lemma rat_fset_of_generators_member_inv : forall d
    (generators : list (QVec d)) (column : 'cV[rat]_d),
    column \in rat_fset_of_generators generators ->
    exists generator : QVec d,
      List.In generator generators /\ column = qvec_to_rat_col generator.
Proof.
  intros d generators. induction generators as [|head tail IH];
    intros column Hin.
  - rewrite /rat_fset_of_generators /rat_fset_of_columns
      /rat_cols_of_list /= in_fset_nil in Hin.
    discriminate.
  - rewrite /rat_fset_of_generators /rat_fset_of_columns
      /rat_cols_of_list /= in_fset_cons in Hin.
    move/orP: Hin => [/eqP Heq | Hin].
    + exists head. split; [now left|exact Heq].
    + destruct (IH column Hin) as [generator [Hmember Heq]].
      exists generator. split; [now right|exact Heq].
Qed.

Lemma rat_fset_of_generators_nil : forall d,
    @rat_fset_of_generators d List.nil = fset0.
Proof.
  intros d. apply/fsetP=> column.
  rewrite /rat_fset_of_generators /rat_fset_of_columns
    rat_cols_of_list_nil in_fset_nil in_fset0.
  reflexivity.
Qed.

Lemma rat_fset_of_generators_permutation : forall d
    (left right : list (QVec d)),
    Permutation left right ->
    rat_fset_of_generators left = rat_fset_of_generators right.
Proof.
  intros d left right Hperm. apply/fsetP=> column. apply/idP/idP; intro Hin.
  - destruct (rat_fset_of_generators_member_inv Hin)
      as [generator [Hmember ->]].
    apply rat_fset_of_generators_member.
    eapply Permutation_in; eauto.
  - destruct (rat_fset_of_generators_member_inv Hin)
      as [generator [Hmember ->]].
    apply rat_fset_of_generators_member.
    eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hmember].
Qed.

Lemma rat_fset_of_generators_duplicate : forall d
    (generator : QVec d) generators,
    rat_fset_of_generators (generator :: generator :: generators) =
      rat_fset_of_generators (generator :: generators).
Proof.
  intros d generator generators. apply/fsetP=> column.
  rewrite /rat_fset_of_generators /rat_fset_of_columns
    /rat_cols_of_list /= !in_fset_cons.
  by rewrite orb_assoc orb_diag.
Qed.

Lemma rat_fset_of_generators_qveceq_duplicate : forall d
    (left right : QVec d) generators,
    QVecEq left right ->
    rat_fset_of_generators (left :: right :: generators) =
      rat_fset_of_generators (left :: generators).
Proof.
  intros d left right generators Heq.
  have Hcol : qvec_to_rat_col left = qvec_to_rat_col right.
  { apply (proj2 (qvec_to_rat_col_eq_iff left right)). exact Heq. }
  apply/fsetP=> column.
  rewrite /rat_fset_of_generators /rat_fset_of_columns
    /rat_cols_of_list /= !in_fset_cons Hcol.
  by rewrite orb_assoc orb_diag.
Qed.

Lemma combine_fsfun_zero : forall (R : ringType) (L : lmodType R),
    @combine R L 0 = 0.
Proof.
  intros R L. rewrite /combine supp_fs0 big_fset0. reflexivity.
Qed.

Lemma combine_fsfun_add : forall (R : ringType) (L : lmodType R)
    (left right : {fsfun L ~> R}),
    combine (left + right) = combine left + combine right.
Proof.
  intros R L left right.
  pose support := (finsupp left `|` finsupp right)%fset.
  have Hadd := @combinewE R L support (left + right) (supp_fsD left right).
  have Hleft := @combinewE R L support left (fsubsetUl _ _).
  have Hright := @combinewE R L support right (fsubsetUr _ _).
  rewrite Hadd Hleft Hright.
  rewrite -big_split /=. apply: eq_bigr=> index _.
  rewrite fsaddE scalerDl. reflexivity.
Qed.

Definition rat_single_weight {d} (column : 'cV[rat]_d)
    (coefficient : rat) : {fsfun 'cV[rat]_d ~> rat} :=
  [fsfun candidate in [fset column]%fset => coefficient].

Lemma rat_single_weightE : forall d (column candidate : 'cV[rat]_d)
    (coefficient : rat),
    rat_single_weight column coefficient candidate =
      if candidate == column then coefficient else 0.
Proof.
  intros d column candidate coefficient.
  rewrite /rat_single_weight fsfunE in_fset1. reflexivity.
Qed.

Lemma rat_single_weight_conic : forall d (column : 'cV[rat]_d)
    (coefficient : rat),
    is_true (((0 : rat) <= coefficient)%R) ->
    conic (rat_single_weight column coefficient).
Proof.
  intros d column coefficient Hnonnegative. apply/conicwP=> candidate.
  rewrite rat_single_weightE. case: eqP=> _; [exact Hnonnegative|exact: lexx].
Qed.

Lemma rat_single_weight_support : forall d (column : 'cV[rat]_d)
    (coefficient : rat),
    (finsupp (rat_single_weight column coefficient) `<=`
      [fset column])%fset.
Proof.
  intros d column coefficient. exact: finsupp_sub.
Qed.

Lemma combine_rat_single_weight : forall d (column : 'cV[rat]_d)
    (coefficient : rat),
    combine (rat_single_weight column coefficient) = coefficient *: column.
Proof.
  intros d column coefficient.
  rewrite (@combinewE _ _ [fset column]%fset
    (rat_single_weight column coefficient)); last exact: rat_single_weight_support.
  rewrite big_fset1 rat_single_weightE eqxx. reflexivity.
Qed.

Fixpoint rat_weight_of_lists {d} (columns : list ('cV[rat]_d))
    (coefficients : list rat) : {fsfun 'cV[rat]_d ~> rat} :=
  match columns, coefficients with
  | column :: columns', coefficient :: coefficients' =>
      rat_single_weight column coefficient +
        rat_weight_of_lists columns' coefficients'
  | _, _ => 0
  end.

Lemma rat_weight_of_lists_conic : forall d
    (columns : list ('cV[rat]_d)) (coefficients : list rat),
    List.length columns = List.length coefficients ->
    List.Forall
      (fun coefficient => is_true (((0 : rat) <= coefficient)%R))
      coefficients ->
    conic (rat_weight_of_lists columns coefficients).
Proof.
  intros d columns. induction columns as [|column columns IH];
    intros [|coefficient coefficients] Hlength Hall; simpl in *;
    try discriminate; try exact: conic0.
  inversion Hlength. inversion Hall; subst.
  apply: conicD.
  - now apply rat_single_weight_conic.
  - now apply IH.
Qed.

Lemma rat_weight_of_lists_support : forall d
    (columns : list ('cV[rat]_d)) (coefficients : list rat),
    List.length columns = List.length coefficients ->
    (finsupp (rat_weight_of_lists columns coefficients) `<=`
      rat_fset_of_columns columns)%fset.
Proof.
  intros d columns. induction columns as [|column columns IH];
    intros [|coefficient coefficients] Hlength; simpl in *; try discriminate.
  - rewrite supp_fs0 /rat_fset_of_columns.
    apply/fsubsetP=> candidate. rewrite in_fset0. discriminate.
  - inversion Hlength as [Htail].
    eapply fsubset_trans; [exact: supp_fsD|].
    rewrite fsubUset. apply/andP. split.
    + eapply fsubset_trans; [exact: rat_single_weight_support|].
      apply/fsubsetP=> candidate.
      rewrite in_fset1 /rat_fset_of_columns in_fset_cons.
      by move/eqP=> ->; rewrite eqxx.
    + eapply fsubset_trans; [exact (IH coefficients Htail)|].
      apply/fsubsetP=> candidate.
      rewrite /rat_fset_of_columns in_fset_cons.
      by move=> Hmember; apply/orP; right.
Qed.

Lemma combine_rat_weight_of_lists : forall d
    (columns : list ('cV[rat]_d)) (coefficients : list rat),
    List.length columns = List.length coefficients ->
    combine (rat_weight_of_lists columns coefficients) =
      rat_linear_combination columns coefficients.
Proof.
  intros d columns. induction columns as [|column columns IH];
    intros [|coefficient coefficients] Hlength; simpl in *; try discriminate.
  - apply combine_fsfun_zero.
  - inversion Hlength as [Htail].
    rewrite combine_fsfun_add combine_rat_single_weight IH; [reflexivity|exact Htail].
Qed.

Fixpoint rat_coefficients_of_weight {d} (columns : list ('cV[rat]_d))
    (weight : {fsfun 'cV[rat]_d ~> rat}) : list rat :=
  match columns with
  | List.nil => List.nil
  | column :: columns' =>
      weight column ::
        rat_coefficients_of_weight columns' [fsfun weight without column]
  end.

Lemma rat_coefficients_of_weight_length : forall d
    (columns : list ('cV[rat]_d)) (weight : {fsfun 'cV[rat]_d ~> rat}),
    List.length (rat_coefficients_of_weight columns weight) =
      List.length columns.
Proof.
  intros d columns. induction columns as [|column columns IH];
    intro weight; simpl; [reflexivity|now rewrite IH].
Qed.

Lemma conic_without : forall (T : choiceType) (weight : {fsfun T ~> rat})
    (point : T),
    conic weight -> conic [fsfun weight without point].
Proof.
  intros T weight point Hconic. apply/conicwP=> candidate.
  rewrite fsfun_withE. case: eqP=> _; [exact: lexx|].
  move/conicwP: Hconic. apply.
Qed.

Lemma rat_coefficients_of_weight_nonnegative : forall d
    (columns : list ('cV[rat]_d)) (weight : {fsfun 'cV[rat]_d ~> rat}),
    conic weight ->
    List.Forall
      (fun coefficient => is_true (((0 : rat) <= coefficient)%R))
      (rat_coefficients_of_weight columns weight).
Proof.
  intros d columns. induction columns as [|column columns IH];
    intros weight Hconic; simpl; constructor.
  - move/conicwP: Hconic. apply.
  - apply IH. now apply conic_without.
Qed.

Lemma fsfun_single_without : forall d
    (weight : {fsfun 'cV[rat]_d ~> rat}) (point : 'cV[rat]_d),
    weight = rat_single_weight point (weight point) +
      [fsfun weight without point].
Proof.
  intros d weight point. apply/fsfunP=> candidate.
  rewrite fsaddE rat_single_weightE fsfun_withE.
  case: eqP=> [->|Hneq].
  - by rewrite addr0.
  - by rewrite add0r.
Qed.

Lemma rat_without_support_tail : forall d (column : 'cV[rat]_d)
    columns (weight : {fsfun 'cV[rat]_d ~> rat}),
    (finsupp weight `<=` rat_fset_of_columns (column :: columns))%fset ->
    (finsupp [fsfun weight without column] `<=`
      rat_fset_of_columns columns)%fset.
Proof.
  intros d column columns weight Hsupport.
  rewrite (finsupp_without weight column column). apply/fsubsetP=> candidate.
  rewrite in_fsetD in_fset1 => /andP [Hneq Hmember].
  move: Hmember => /(fsubsetP Hsupport).
  rewrite /rat_fset_of_columns in_fset_cons => /orP [/eqP Heq|Htail].
  - subst candidate. by rewrite eqxx in Hneq.
  - exact Htail.
Qed.

Lemma rat_linear_combination_coefficients_of_weight : forall d
    (columns : list ('cV[rat]_d)) (weight : {fsfun 'cV[rat]_d ~> rat}),
    (finsupp weight `<=` rat_fset_of_columns columns)%fset ->
    rat_linear_combination columns
      (rat_coefficients_of_weight columns weight) = combine weight.
Proof.
  intros d columns. induction columns as [|column columns IH];
    intros weight Hsupport; simpl.
  - have Hempty : @rat_fset_of_columns d List.nil = fset0.
    { apply/fsetP=> candidate.
      rewrite /rat_fset_of_columns in_fset_nil in_fset0. reflexivity. }
    rewrite Hempty in Hsupport.
    rewrite (@combinewE _ _ fset0 weight).
    + rewrite big_fset0. reflexivity.
    + exact Hsupport.
  - rewrite (IH [fsfun weight without column]);
      last now apply rat_without_support_tail.
    rewrite -(combine_rat_single_weight column (weight column))
      -combine_fsfun_add.
    apply f_equal. symmetry. apply fsfun_single_without.
Qed.

Theorem rat_columns_polyhedra_cone : forall d
    (columns : list ('cV[rat]_d)) (value : 'cV[rat]_d),
    value \in polyhedron.cone (rat_fset_of_columns columns) <->
    exists coefficients : list rat,
      List.length coefficients = List.length columns /\
      List.Forall
        (fun coefficient => is_true (((0 : rat) <= coefficient)%R))
        coefficients /\
      value = rat_linear_combination columns coefficients.
Proof.
  intros d columns value. split.
  - move/polyhedron.in_coneP=> [weight Hsupport Hvalue].
    exists (rat_coefficients_of_weight columns weight). repeat split.
    + apply rat_coefficients_of_weight_length.
    + apply rat_coefficients_of_weight_nonnegative. exact (valP weight).
    + rewrite Hvalue.
      symmetry. apply rat_linear_combination_coefficients_of_weight.
      exact Hsupport.
  - intros [coefficients [Hlength [Hnonnegative Hvalue]]].
    have Hlength' : List.length columns = List.length coefficients.
    { symmetry. exact Hlength. }
    apply/polyhedron.in_coneP.
    exists (mkConicFun
      (rat_weight_of_lists_conic Hlength' Hnonnegative)).
    + exact (rat_weight_of_lists_support Hlength').
    + rewrite Hvalue combine_rat_weight_of_lists; [reflexivity|exact Hlength'].
Qed.

Lemma rat_to_q_coefficients_nonnegative : forall coefficients : list rat,
    List.Forall
      (fun coefficient => is_true (((0 : rat) <= coefficient)%R))
      coefficients ->
    List.Forall (fun coefficient : Q => Qle 0 coefficient)
      (List.map rat_to_q coefficients).
Proof.
  intros coefficients Hall. induction Hall as [|coefficient coefficients Hhead Htail IH].
  - constructor.
  - simpl. constructor.
    + now apply rat_to_q_nonnegative.
    + exact IH.
Qed.

Lemma q_to_rat_after_rat_to_q_list : forall coefficients : list rat,
    List.map q_to_rat (List.map rat_to_q coefficients) = coefficients.
Proof.
  intros coefficients. induction coefficients as [|coefficient coefficients IH].
  - reflexivity.
  - simpl. rewrite rat_to_q_to_rat IH. reflexivity.
Qed.

Theorem qcone_generated_polyhedra_cone : forall d
    (generators : list (QVec d)) (value : QVec d),
    qcone_generated generators value <->
    qvec_to_rat_col value \in
      polyhedron.cone (rat_fset_of_generators generators).
Proof.
  intros d generators value. split.
  - intro Hcone.
    apply qcone_generated_aligned_coefficients in Hcone as
      [coefficients [Hlength [Hnonnegative Hvalue]]].
    apply (proj2 (rat_columns_polyhedra_cone
      (rat_cols_of_list generators) (qvec_to_rat_col value))).
    exists (List.map q_to_rat coefficients). repeat split.
    + rewrite List.map_length rat_cols_of_list_length. exact Hlength.
    + apply (proj1 (q_to_rat_coefficients_nonnegative_iff coefficients)).
      exact Hnonnegative.
    + have Hconverted :
        qvec_to_rat_col value =
          qvec_to_rat_col (qlinear_combination generators coefficients).
      { apply (proj2 (qvec_to_rat_col_eq_iff value
          (qlinear_combination generators coefficients))). exact Hvalue. }
      rewrite Hconverted.
      apply qvec_to_rat_linear_combination. symmetry. exact Hlength.
  - intro Hcone.
    apply (proj1 (rat_columns_polyhedra_cone
      (rat_cols_of_list generators) (qvec_to_rat_col value))) in Hcone.
    destruct Hcone as [coefficients [Hlength [Hnonnegative Hvalue]]].
    apply qcone_generated_aligned_coefficients.
    exists (List.map rat_to_q coefficients). repeat split.
    + rewrite List.map_length in Hlength |- *.
      rewrite rat_cols_of_list_length in Hlength. exact Hlength.
    + now apply rat_to_q_coefficients_nonnegative.
    + apply (proj1 (qvec_to_rat_col_eq_iff value
        (qlinear_combination generators (List.map rat_to_q coefficients)))).
      rewrite qvec_to_rat_linear_combination.
      * rewrite q_to_rat_after_rat_to_q_list. exact Hvalue.
      * rewrite List.map_length.
        rewrite rat_cols_of_list_length in Hlength.
        symmetry. exact Hlength.
Qed.
