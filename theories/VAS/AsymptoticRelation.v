From Coq Require Import Fin Lia List QArith Vector.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Cone LatticeGordanPullback MathCompBridge
  QConeCore RationalDefinability RationalHToV.
From Mell.Order Require Import PeriodicOrder.
From Mell.VAS Require Import RelationCone Runs Transformer.

Open Scope Q_scope.

Definition qreindex_variable {source target}
    (selection : Fin.t source -> Fin.t target) (bound variable : nat) : nat :=
  match lt_dec variable bound with
  | left _ => variable
  | right _ =>
      match lt_dec (variable - bound) source with
      | left proof =>
          (bound + proj1_sig (Fin.to_nat
            (selection (Fin.of_nat_lt proof))))%nat
      | right _ => variable
      end
  end.

Fixpoint qterm_reindex {source target}
    (selection : Fin.t source -> Fin.t target) (bound : nat)
    (term : QTerm) : QTerm :=
  match term with
  | QTVar variable => QTVar (qreindex_variable selection bound variable)
  | QTConst constant => QTConst constant
  | QTAdd lhs rhs =>
      QTAdd (qterm_reindex selection bound lhs)
        (qterm_reindex selection bound rhs)
  | QTOpp value => QTOpp (qterm_reindex selection bound value)
  | QTScale coefficient value =>
      QTScale coefficient (qterm_reindex selection bound value)
  end.

Fixpoint qformula_reindex {source target}
    (selection : Fin.t source -> Fin.t target) (bound : nat)
    (formula : QFormula) : QFormula :=
  match formula with
  | QFTop => QFTop
  | QFBot => QFBot
  | QFEq lhs rhs =>
      QFEq (@qterm_reindex source target selection bound lhs)
        (@qterm_reindex source target selection bound rhs)
  | QFLt lhs rhs =>
      QFLt (@qterm_reindex source target selection bound lhs)
        (@qterm_reindex source target selection bound rhs)
  | QFLe lhs rhs =>
      QFLe (@qterm_reindex source target selection bound lhs)
        (@qterm_reindex source target selection bound rhs)
  | QFAnd lhs rhs =>
      QFAnd (@qformula_reindex source target selection bound lhs)
        (@qformula_reindex source target selection bound rhs)
  | QFOr lhs rhs =>
      QFOr (@qformula_reindex source target selection bound lhs)
        (@qformula_reindex source target selection bound rhs)
  | QFNot body => QFNot (@qformula_reindex source target selection bound body)
  | QFExists body =>
      QFExists (@qformula_reindex source target selection (S bound) body)
  | QFForall body =>
      QFForall (@qformula_reindex source target selection (S bound) body)
  end.

Lemma qterm_reindex_closed : forall source target
    (selection : Fin.t source -> Fin.t target) bound term,
    qterm_closed (bound + source) term = true ->
    qterm_closed (bound + target)
      (qterm_reindex selection bound term) = true.
Proof.
  intros source target selection bound term. revert bound.
  induction term; intros bound Hclosed; cbn in *; auto.
  - apply Nat.ltb_lt in Hclosed. unfold qreindex_variable.
    destruct (lt_dec n bound) as [Hbound|Hbound].
    + apply Nat.ltb_lt. lia.
    + destruct (lt_dec (n - bound) source) as [Hsource|Hsource].
      * apply Nat.ltb_lt. pose proof
          (proj2_sig (Fin.to_nat (selection (Fin.of_nat_lt Hsource)))) as Hindex.
        apply (proj1 (Nat.add_lt_mono_l _ _ bound)). exact Hindex.
      * lia.
  - apply andb_true_iff in Hclosed as [Hleft Hright].
    apply andb_true_iff. split; [apply IHterm1|apply IHterm2]; assumption.
Qed.

Lemma qformula_reindex_closed : forall source target
    (selection : Fin.t source -> Fin.t target) bound formula,
    qformula_closed (bound + source) formula = true ->
    qformula_closed (bound + target)
      (qformula_reindex selection bound formula) = true.
Proof.
  intros source target selection bound formula. revert bound.
  induction formula; intros bound Hclosed; cbn in *; auto;
    try (apply andb_true_iff in Hclosed as [Hleft Hright];
      apply andb_true_iff; split;
      [eapply qterm_reindex_closed|eapply qterm_reindex_closed]; eauto);
    try (apply andb_true_iff in Hclosed as [Hleft Hright];
      apply andb_true_iff; split;
      [apply IHformula1|apply IHformula2]; assumption).
  - apply (IHformula (S bound)). exact Hclosed.
  - apply (IHformula (S bound)). exact Hclosed.
Qed.

Definition qenvironment_reindex_agree {source target}
    (selection : Fin.t source -> Fin.t target) (bound : nat)
    (original transformed : QEnvironment) : Prop :=
  (forall variable, (variable < bound)%nat ->
      original variable = transformed variable) /\
  forall index : Fin.t source,
    original (bound + proj1_sig (Fin.to_nat index))%nat =
    transformed (bound + proj1_sig (Fin.to_nat (selection index)))%nat.

Lemma qenvironment_reindex_extend : forall source target
    (selection : Fin.t source -> Fin.t target) bound
    original transformed value,
    qenvironment_reindex_agree selection bound original transformed ->
    qenvironment_reindex_agree selection (S bound)
      (qenvironment_extend original value)
      (qenvironment_extend transformed value).
Proof.
  intros source target selection bound original transformed value [Hbound Hfree].
  split.
  - intros [|variable] Hvariable; cbn; [reflexivity|]. apply Hbound. lia.
  - intro index. cbn. apply Hfree.
Qed.

Lemma qterm_reindex_semantics : forall source target
    (selection : Fin.t source -> Fin.t target) bound term
    original transformed,
    qterm_closed (bound + source) term = true ->
    qenvironment_reindex_agree selection bound original transformed ->
    qterm_semantics original term =
      qterm_semantics transformed (qterm_reindex selection bound term).
Proof.
  intros source target selection bound term. revert bound.
  induction term as [variable|constant|left IHleft right IHright|value IHopp|
      coefficient value IHscale];
    intros bound original transformed Hclosed [Hbound Hfree];
    cbn in *.
  - apply Nat.ltb_lt in Hclosed. unfold qreindex_variable.
    destruct (lt_dec variable bound) as [Hin|Hin].
    + apply Hbound. exact Hin.
    + destruct (lt_dec (variable - bound) source) as [Hsource|Hsource].
      * specialize (Hfree (Fin.of_nat_lt Hsource)).
        rewrite Fin.to_nat_of_nat in Hfree.
        cbn in Hfree.
        replace (bound + (variable - bound))%nat with variable in Hfree by lia.
        exact Hfree.
      * lia.
  - reflexivity.
  - apply andb_true_iff in Hclosed as [Hleft Hright].
    rewrite (IHleft bound original transformed Hleft (conj Hbound Hfree)),
      (IHright bound original transformed Hright (conj Hbound Hfree)).
    reflexivity.
  - rewrite (IHopp bound original transformed Hclosed (conj Hbound Hfree)).
    reflexivity.
  - rewrite (IHscale bound original transformed Hclosed (conj Hbound Hfree)).
    reflexivity.
Qed.

Lemma qformula_reindex_semantics : forall source target
    (selection : Fin.t source -> Fin.t target) bound formula
    original transformed,
    qformula_closed (bound + source) formula = true ->
    qenvironment_reindex_agree selection bound original transformed ->
    (qformula_semantics original formula <->
     qformula_semantics transformed (qformula_reindex selection bound formula)).
Proof.
  intros source target selection bound formula. revert bound.
  induction formula as [| |left right|left right|left right|
      left IHleft right IHright|left IHleft right IHright|
      body IHbody|body IHbody|body IHbody];
    intros bound original transformed Hclosed Hagree; cbn in *.
  - tauto.
  - tauto.
  - apply andb_true_iff in Hclosed as [Hl Hr].
    rewrite <- (qterm_reindex_semantics _ _ _ _ _ _ _ Hl Hagree),
      <- (qterm_reindex_semantics _ _ _ _ _ _ _ Hr Hagree). reflexivity.
  - apply andb_true_iff in Hclosed as [Hl Hr].
    rewrite <- (qterm_reindex_semantics _ _ _ _ _ _ _ Hl Hagree),
      <- (qterm_reindex_semantics _ _ _ _ _ _ _ Hr Hagree). reflexivity.
  - apply andb_true_iff in Hclosed as [Hl Hr].
    rewrite <- (qterm_reindex_semantics _ _ _ _ _ _ _ Hl Hagree),
      <- (qterm_reindex_semantics _ _ _ _ _ _ _ Hr Hagree). reflexivity.
  - apply andb_true_iff in Hclosed as [Hl Hr].
    rewrite (IHleft bound original transformed Hl Hagree),
      (IHright bound original transformed Hr Hagree). tauto.
  - apply andb_true_iff in Hclosed as [Hl Hr].
    rewrite (IHleft bound original transformed Hl Hagree),
      (IHright bound original transformed Hr Hagree). tauto.
  - rewrite (IHbody bound original transformed Hclosed Hagree). tauto.
  - assert (Hextend : forall value,
        qenvironment_reindex_agree selection (S bound)
          (qenvironment_extend original value)
          (qenvironment_extend transformed value)).
    { intro value. now apply qenvironment_reindex_extend. }
    split; intros [value Hvalue]; exists value.
    + apply (proj1 (IHbody (S bound) _ _ Hclosed (Hextend value))). exact Hvalue.
    + apply (proj2 (IHbody (S bound) _ _ Hclosed (Hextend value))). exact Hvalue.
  - assert (Hextend : forall value,
        qenvironment_reindex_agree selection (S bound)
          (qenvironment_extend original value)
          (qenvironment_extend transformed value)).
    { intro value. now apply qenvironment_reindex_extend. }
    split; intros Hall value.
    + apply (proj1 (IHbody (S bound) _ _ Hclosed (Hextend value))). apply Hall.
    + apply (proj2 (IHbody (S bound) _ _ Hclosed (Hextend value))). apply Hall.
Qed.

Theorem qdefinable_coordinate_preimage : forall source target
    (selection : Fin.t source -> Fin.t target) (set : QSet source),
    QDefinable set ->
    QDefinable (fun value => set (fun index => value (selection index))).
Proof.
  intros source target selection set [formula [Hclosed Hformula]].
  exists (qformula_reindex selection 0 formula). split.
  - exact (qformula_reindex_closed source target selection 0 formula Hclosed).
  - intro value. rewrite Hformula.
    apply (qformula_reindex_semantics source target selection 0 formula
      (qvec_environment (fun index => value (selection index)))
      (qvec_environment value)); [exact Hclosed|].
    split.
    + intros variable Hvariable. lia.
    + intro index. cbn.
      rewrite !qvec_environment_inside. reflexivity.
Qed.

Definition qtriple_pack {d} (first second third : QVec d) : QVec ((d + d) + d) :=
  qvec_join (qpair_pack first second) third.

Definition qtriple_xy_selection (d : nat) :
    Fin.t (d + d) -> Fin.t ((d + d) + d) := fun index => Fin.L d index.

Lemma qtriple_shift_bound : forall d (index : Fin.t (d + d)),
    (d + proj1_sig (Fin.to_nat index) < (d + d) + d)%nat.
Proof.
  intros d index. replace ((d + d) + d)%nat with (d + (d + d))%nat by lia.
  apply (proj1 (Nat.add_lt_mono_l _ _ d)). exact (proj2_sig (Fin.to_nat index)).
Qed.

Lemma qtriple_direct_bound : forall d (index : Fin.t (d + d)),
    (proj1_sig (Fin.to_nat index) < (d + d) + d)%nat.
Proof.
  intros d index. eapply Nat.lt_le_trans.
  - exact (proj2_sig (Fin.to_nat index)).
  - lia.
Qed.

Definition qtriple_yz_selection (d : nat) :
    Fin.t (d + d) -> Fin.t ((d + d) + d) := fun index =>
  Fin.of_nat_lt (p := d + proj1_sig (Fin.to_nat index))
    (qtriple_shift_bound d index).

Definition qtriple_xz_selection (d : nat) :
    Fin.t (d + d) -> Fin.t ((d + d) + d) := fun index =>
  if lt_dec (proj1_sig (Fin.to_nat index)) d
  then Fin.of_nat_lt (p := proj1_sig (Fin.to_nat index))
    (qtriple_direct_bound d index)
  else Fin.of_nat_lt (p := d + proj1_sig (Fin.to_nat index))
    (qtriple_shift_bound d index).

Lemma qtriple_yz_selection_left : forall d (index : Fin.t d),
    qtriple_yz_selection d (Fin.L d index) = Fin.L d (Fin.R d index).
Proof.
  intros d index. apply Fin.to_nat_inj. unfold qtriple_yz_selection.
  pose proof (@Fin.to_nat_of_nat
    (d + proj1_sig (Fin.to_nat (Fin.L d index))) ((d + d) + d)
    (qtriple_shift_bound d (Fin.L d index))) as Hselected.
  rewrite Hselected. cbn.
  rewrite (Fin.L_sanity d index), (Fin.L_sanity d (Fin.R d index)),
    (Fin.R_sanity d index). reflexivity.
Qed.

Lemma qtriple_yz_selection_right : forall d (index : Fin.t d),
    qtriple_yz_selection d (Fin.R d index) = Fin.R (d + d) index.
Proof.
  intros d index. apply Fin.to_nat_inj. unfold qtriple_yz_selection.
  pose proof (@Fin.to_nat_of_nat
    (d + proj1_sig (Fin.to_nat (Fin.R d index))) ((d + d) + d)
    (qtriple_shift_bound d (Fin.R d index))) as Hselected.
  rewrite Hselected. cbn.
  rewrite (Fin.R_sanity d index), (Fin.R_sanity (d + d) index). lia.
Qed.

Lemma qtriple_xz_selection_left : forall d (index : Fin.t d),
    qtriple_xz_selection d (Fin.L d index) = Fin.L d (Fin.L d index).
Proof.
  intros d index. apply Fin.to_nat_inj. unfold qtriple_xz_selection.
  destruct (lt_dec (proj1_sig (Fin.to_nat (Fin.L d index))) d)
    as [Hlt|Hlt].
  - pose proof (@Fin.to_nat_of_nat
      (proj1_sig (Fin.to_nat (Fin.L d index))) ((d + d) + d)
      (qtriple_direct_bound d (Fin.L d index))) as Hselected.
    rewrite Hselected. cbn.
    rewrite (Fin.L_sanity d index), (Fin.L_sanity d (Fin.L d index)),
      (Fin.L_sanity d index). reflexivity.
  - exfalso. apply Hlt. rewrite (Fin.L_sanity d index).
    exact (proj2_sig (Fin.to_nat index)).
Qed.

Lemma qtriple_xz_selection_right : forall d (index : Fin.t d),
    qtriple_xz_selection d (Fin.R d index) = Fin.R (d + d) index.
Proof.
  intros d index. apply Fin.to_nat_inj. unfold qtriple_xz_selection.
  destruct (lt_dec (proj1_sig (Fin.to_nat (Fin.R d index))) d)
    as [Hlt|Hlt].
  - rewrite (Fin.R_sanity d index) in Hlt. lia.
  - pose proof (@Fin.to_nat_of_nat
      (d + proj1_sig (Fin.to_nat (Fin.R d index))) ((d + d) + d)
      (qtriple_shift_bound d (Fin.R d index))) as Hselected.
    rewrite Hselected. cbn.
    rewrite (Fin.R_sanity d index), (Fin.R_sanity (d + d) index). lia.
Qed.

Lemma qtriple_pack_xy : forall d (first second third : QVec d),
    QVecEq
      (fun index => qtriple_pack first second third
        (qtriple_xy_selection d index))
      (qpair_pack first second).
Proof.
  intros d first second third index. unfold qtriple_pack, qtriple_xy_selection,
    qvec_join, qvec_of_vector.
  rewrite VectorSpec.nth_append_L, qvec_to_vector_nth. reflexivity.
Qed.

Lemma qtriple_pack_yz : forall d (first second third : QVec d),
    QVecEq
      (fun index => qtriple_pack first second third
        (qtriple_yz_selection d index))
      (qpair_pack second third).
Proof.
  intros d first second third index.
  refine (Fin.case_L_R' (fun index =>
    qtriple_pack first second third (qtriple_yz_selection d index) ==
      qpair_pack second third index) index _ _); intro component.
  - rewrite qtriple_yz_selection_left.
    unfold qtriple_pack, qpair_pack, qvec_join, qvec_of_vector. cbn.
    repeat first [rewrite VectorSpec.nth_append_L |
      rewrite VectorSpec.nth_append_R | rewrite qvec_to_vector_nth]. reflexivity.
  - rewrite qtriple_yz_selection_right.
    unfold qtriple_pack, qpair_pack, qvec_join, qvec_of_vector. cbn.
    repeat first [rewrite VectorSpec.nth_append_L |
      rewrite VectorSpec.nth_append_R | rewrite qvec_to_vector_nth]. reflexivity.
Qed.

Lemma qtriple_pack_xz : forall d (first second third : QVec d),
    QVecEq
      (qpair_pack first third)
      (fun index => qtriple_pack first second third
        (qtriple_xz_selection d index)).
Proof.
  intros d first second third index.
  refine (Fin.case_L_R' (fun index =>
    qpair_pack first third index ==
      qtriple_pack first second third (qtriple_xz_selection d index))
    index _ _); intro component.
  - rewrite qtriple_xz_selection_left.
    unfold qtriple_pack, qpair_pack, qvec_join, qvec_of_vector. cbn.
    repeat first [rewrite VectorSpec.nth_append_L |
      rewrite VectorSpec.nth_append_R | rewrite qvec_to_vector_nth]. reflexivity.
  - rewrite qtriple_xz_selection_right.
    unfold qtriple_pack, qpair_pack, qvec_join, qvec_of_vector. cbn.
    repeat first [rewrite VectorSpec.nth_append_L |
      rewrite VectorSpec.nth_append_R | rewrite qvec_to_vector_nth]. reflexivity.
Qed.

Definition qtriple_first {d} (value : QVec ((d + d) + d)) : QVec d :=
  fun index => value (Fin.L d (Fin.L d index)).

Definition qtriple_second {d} (value : QVec ((d + d) + d)) : QVec d :=
  fun index => value (Fin.L d (Fin.R d index)).

Definition qtriple_third {d} (value : QVec ((d + d) + d)) : QVec d :=
  fun index => value (Fin.R (d + d) index).

Lemma qtriple_xy_reconstruct : forall d (value : QVec ((d + d) + d)),
    QVecEq
      (fun index => value (qtriple_xy_selection d index))
      (qpair_pack (qtriple_first value) (qtriple_second value)).
Proof.
  intros d value index.
  refine (Fin.case_L_R' (fun index =>
    value (qtriple_xy_selection d index) ==
      qpair_pack (qtriple_first value) (qtriple_second value) index)
    index _ _); intro component;
    unfold qtriple_xy_selection, qtriple_first, qtriple_second,
      qpair_pack, qvec_join, qvec_of_vector; cbn.
  - rewrite VectorSpec.nth_append_L, qvec_to_vector_nth. reflexivity.
  - rewrite VectorSpec.nth_append_R, qvec_to_vector_nth. reflexivity.
Qed.

Lemma qtriple_yz_reconstruct : forall d (value : QVec ((d + d) + d)),
    QVecEq
      (fun index => value (qtriple_yz_selection d index))
      (qpair_pack (qtriple_second value) (qtriple_third value)).
Proof.
  intros d value index.
  refine (Fin.case_L_R' (fun index =>
    value (qtriple_yz_selection d index) ==
      qpair_pack (qtriple_second value) (qtriple_third value) index)
    index _ _); intro component;
    unfold qtriple_second, qtriple_third, qpair_pack, qvec_join,
      qvec_of_vector; cbn.
  - rewrite qtriple_yz_selection_left,
      VectorSpec.nth_append_L, qvec_to_vector_nth. reflexivity.
  - rewrite qtriple_yz_selection_right,
      VectorSpec.nth_append_R, qvec_to_vector_nth. reflexivity.
Qed.

Lemma qtriple_xz_reconstruct : forall d (value : QVec ((d + d) + d)),
    QVecEq
      (fun index => value (qtriple_xz_selection d index))
      (qpair_pack (qtriple_first value) (qtriple_third value)).
Proof.
  intros d value index.
  refine (Fin.case_L_R' (fun index =>
    value (qtriple_xz_selection d index) ==
      qpair_pack (qtriple_first value) (qtriple_third value) index)
    index _ _); intro component;
    unfold qtriple_first, qtriple_third, qpair_pack, qvec_join,
      qvec_of_vector; cbn.
  - rewrite qtriple_xz_selection_left,
      VectorSpec.nth_append_L, qvec_to_vector_nth. reflexivity.
  - rewrite qtriple_xz_selection_right,
      VectorSpec.nth_append_R, qvec_to_vector_nth. reflexivity.
Qed.

Definition QSetExtensional {d} (set : QSet d) : Prop :=
  forall left right, QVecEq left right -> (set left <-> set right).

Lemma qdefinable_congr : forall d (left right : QSet d),
    (forall value, left value <-> right value) ->
    QDefinable left -> QDefinable right.
Proof.
  intros d left right Hsame [formula [Hclosed Hformula]].
  exists formula. split; [exact Hclosed|]. intro value.
  rewrite <- Hformula. symmetry. apply Hsame.
Qed.

Theorem qdefinable_relation_compose : forall d
    (left right : QSet (d + d)),
    QSetExtensional left -> QSetExtensional right ->
    QDefinable left -> QDefinable right ->
    QDefinable (fun pair => exists middle : QVec d,
      left (qpair_pack (qpair_left pair) middle) /\
      right (qpair_pack middle (qpair_right pair))).
Proof.
  intros d left right Hleft_ext Hright_ext Hleft_def Hright_def.
  pose proof (qdefinable_coordinate_preimage (d + d) ((d + d) + d)
    (qtriple_xy_selection d) left Hleft_def) as Hxy.
  pose proof (qdefinable_coordinate_preimage (d + d) ((d + d) + d)
    (qtriple_yz_selection d) right Hright_def) as Hyz.
  pose proof (qdefinable_intersection ((d + d) + d) _ _ Hxy Hyz) as Htriple.
  pose proof (qdefinable_projection ((d + d) + d) (d + d)
    (qtriple_xz_selection d) _ Htriple) as Hprojected.
  eapply (qdefinable_congr (d + d)); [|exact Hprojected].
  intro pair. symmetry. split.
  - intros [middle [Hleft Hright]].
    exists (qtriple_pack (qpair_left pair) middle (qpair_right pair)). split.
    + split.
      * apply (proj2 (Hleft_ext _ _
          (qtriple_pack_xy d _ _ _))). exact Hleft.
      * apply (proj2 (Hright_ext _ _
          (qtriple_pack_yz d _ _ _))). exact Hright.
    + eapply qvec_eq_trans; [apply qpair_pack_split|].
      apply qtriple_pack_xz.
  - intros [triple [[Hleft Hright] Hcoordinates]].
    exists (qtriple_second triple). split.
    + apply (proj1 (Hleft_ext _ _ (qtriple_xy_reconstruct d triple))) in Hleft.
      assert (Hpair : QVecEq pair
          (qpair_pack (qtriple_first triple) (qtriple_third triple))).
      { eapply qvec_eq_trans; [exact Hcoordinates|].
        apply qtriple_xz_reconstruct. }
      assert (Hpacked : QVecEq
          (qpair_pack (qpair_left pair) (qpair_right pair))
          (qpair_pack (qtriple_first triple) (qtriple_third triple))).
      { eapply qvec_eq_trans.
        - apply qvec_eq_sym, qpair_pack_split.
        - exact Hpair. }
      apply qpair_pack_components in Hpacked as [Hfirst _].
      apply (proj2 (Hleft_ext _ _
        (qpair_pack_ext d _ _ _ _ Hfirst (qvec_eq_refl _ _)))). exact Hleft.
    + apply (proj1 (Hright_ext _ _ (qtriple_yz_reconstruct d triple))) in Hright.
      assert (Hpair : QVecEq pair
          (qpair_pack (qtriple_first triple) (qtriple_third triple))).
      { eapply qvec_eq_trans; [exact Hcoordinates|].
        apply qtriple_xz_reconstruct. }
      assert (Hpacked : QVecEq
          (qpair_pack (qpair_left pair) (qpair_right pair))
          (qpair_pack (qtriple_first triple) (qtriple_third triple))).
      { eapply qvec_eq_trans.
        - apply qvec_eq_sym, qpair_pack_split.
        - exact Hpair. }
      apply qpair_pack_components in Hpacked as [_ Hthird].
      apply (proj2 (Hright_ext _ _
        (qpair_pack_ext d _ _ _ _ (qvec_eq_refl _ _) Hthird))). exact Hright.
Qed.

Definition RelationConePairs {d} (R : ZRelation d) : QSet (d + d) :=
  fun pair => Cone (ZRelationPairs R) pair.

Lemma relation_cone_pairs_extensional : forall d (R : ZRelation d),
    QSetExtensional (RelationConePairs R).
Proof.
  intros d R left right Heq. unfold RelationConePairs.
  now apply cone_qvec_ext_relation.
Qed.

Lemma relation_cone_pairs_unpack : forall d (R : ZRelation d) pair,
    RelationConePairs R pair <->
    RationalRelationCone R (qpair_left pair) (qpair_right pair).
Proof.
  intros d R pair. unfold RelationConePairs, RationalRelationCone.
  apply cone_qvec_ext_relation. apply qpair_pack_split.
Qed.

Lemma conegen_same_generators : forall d (left right : ZSet d),
    SameSet left right -> forall point,
      ConeGen left point <-> ConeGen right point.
Proof.
  intros d left right Hsame point. split; intro Hgenerated.
  - induction Hgenerated.
    + constructor.
    + apply cone_add; [exact H|apply Hsame, H0|exact IHHgenerated].
  - induction Hgenerated.
    + constructor.
    + apply cone_add; [exact H|apply Hsame, H0|exact IHHgenerated].
Qed.

Lemma cone_same_generators : forall d (left right : ZSet d),
    SameSet left right -> forall point,
      Cone left point <-> Cone right point.
Proof.
  intros d left right Hsame point. split;
    intros [generated [Hgenerated Hpoint]]; exists generated; split;
    [apply (proj1 (conegen_same_generators d left right Hsame generated))|
     exact Hpoint|
     apply (proj2 (conegen_same_generators d left right Hsame generated))|
     exact Hpoint]; assumption.
Qed.

Definition AsymptoticallyDefinableZRelation {d} (R : ZRelation d) : Prop :=
  PeriodicZRelation R /\ QDefinable (RelationConePairs R).

Definition AsymptoticallyDefinableNRelation {d} (R : NRelation d) : Prop :=
  PeriodicNRelation R /\
  QDefinable (RelationConePairs (NRelationAsZ R)).

Theorem lemma_5_1_asymptotic_relation_compose : forall d
    (R S : ZRelation d),
    AsymptoticallyDefinableZRelation R ->
    AsymptoticallyDefinableZRelation S ->
    AsymptoticallyDefinableZRelation (ZRelCompose R S).
Proof.
  intros d R S [HRperiodic HRdef] [HSperiodic HSdef]. split.
  - now apply periodic_zrelation_compose.
  - assert (Hcomposed : QDefinable (fun pair => exists middle : QVec d,
        RelationConePairs R (qpair_pack (qpair_left pair) middle) /\
        RelationConePairs S (qpair_pack middle (qpair_right pair)))).
    { apply qdefinable_relation_compose;
        try apply relation_cone_pairs_extensional; assumption. }
    eapply (qdefinable_congr (d + d)); [|exact Hcomposed]. intro pair.
    rewrite relation_cone_pairs_unpack.
    rewrite (periodic_relation_cone_compose d R S HRperiodic HSperiodic).
    reflexivity.
Qed.

Lemma asymptotic_zrelation_congr : forall d (R S : ZRelation d),
    ZRelSame R S ->
    AsymptoticallyDefinableZRelation R ->
    AsymptoticallyDefinableZRelation S.
Proof.
  intros d R S Hsame [HRperiodic HRdef]. split.
  - apply (proj2 (periodic_zrelation_pairs_iff d S)).
    apply (proj1 (periodic_zrelation_pairs_iff d R)) in HRperiodic.
    split.
    + apply (proj1 (zrelation_same_pairs d R S)) in Hsame.
      apply Hsame, HRperiodic.
    + intros left right Hleft Hright.
      apply (proj1 (zrelation_same_pairs d R S)) in Hsame.
      apply Hsame. apply HRperiodic; now apply Hsame.
  - eapply (qdefinable_congr (d + d)); [|exact HRdef]. intro point.
    apply cone_same_generators.
    now apply (proj1 (zrelation_same_pairs d R S)).
Qed.

Theorem lemma_5_1_nrelation_compose : forall d (R S : NRelation d),
    AsymptoticallyDefinableNRelation R ->
    AsymptoticallyDefinableNRelation S ->
    AsymptoticallyDefinableNRelation (NRelCompose R S).
Proof.
  intros d R S [HRperiodic HRdef] [HSperiodic HSdef]. split.
  - now apply periodic_nrelation_compose.
  - assert (HRasym : AsymptoticallyDefinableZRelation (NRelationAsZ R)).
    { split; [now apply periodic_nrelation_as_z|exact HRdef]. }
    assert (HSasym : AsymptoticallyDefinableZRelation (NRelationAsZ S)).
    { split; [now apply periodic_nrelation_as_z|exact HSdef]. }
    pose proof (lemma_5_1_asymptotic_relation_compose d _ _
      HRasym HSasym) as Hcompose.
    apply (asymptotic_zrelation_congr d
      (ZRelCompose (NRelationAsZ R) (NRelationAsZ S))
      (NRelationAsZ (NRelCompose R S))).
    + intros input output. symmetry. apply nrelation_as_z_compose.
    + exact Hcompose.
Qed.

Theorem transformer_along_targets_asymptotic_of_capacities : forall d
    (system : PlainVAS d) current targets,
    (forall capacity,
      List.In capacity (current :: targets) ->
      AsymptoticallyDefinableNRelation
        (CapacityTransformer system capacity)) ->
    AsymptoticallyDefinableNRelation
      (TransformerAlongTargets system current targets).
Proof.
  intros d system current targets. revert current.
  induction targets as [|target tail IH]; intros current Hall; cbn.
  - apply Hall. now left.
  - apply lemma_5_1_nrelation_compose.
    + apply Hall. now left.
    + apply IH. intros capacity Hcapacity. apply Hall. now right.
Qed.

Theorem transformer_along_run_asymptotic_of_capacities : forall d
    (system : PlainVAS d) (run : VASRun d),
    (forall capacity,
      List.In capacity (RunSource run :: RunTargets run) ->
      AsymptoticallyDefinableNRelation
        (CapacityTransformer system capacity)) ->
    AsymptoticallyDefinableNRelation
      (TransformerAlongRun system run).
Proof.
  intros d system run Hall. unfold TransformerAlongRun.
  now apply transformer_along_targets_asymptotic_of_capacities.
Qed.
