From Coq Require Import List Lia Classical_Prop Logic.ConstructiveEpsilon.
From KruskalAfProp Require Import af.af.
From Mell.Order Require Import AlmostFullBridge.

Import ListNotations.

Section CountableFiniteBasis.

Context {X : Type}.
Variable enumerate : nat -> option X.
Variable P : X -> Prop.
Variable R : X -> X -> Prop.
Variable R_dec : forall left right, {R left right} + {~ R left right}.

Definition avoids (basis : list {value : X | P value})
    (candidate : X) : Prop :=
  forall base, List.In base basis -> ~ R (proj1_sig base) candidate.

Fixpoint avoidsb (basis : list {value : X | P value})
    (candidate : X) : bool :=
  match basis with
  | [] => true
  | base :: tail =>
      if R_dec (proj1_sig base) candidate then false else avoidsb tail candidate
  end.

Lemma avoidsb_true_iff : forall basis candidate,
    avoidsb basis candidate = true <-> avoids basis candidate.
Proof.
  intros basis candidate. induction basis as [|base tail IH]; cbn.
  - split; [intros _ element Hin; contradiction|reflexivity].
  - destruct (R_dec (proj1_sig base) candidate) as [Hrel|Hrel].
    + split; [discriminate|].
      intro Havoid. exfalso. exact (Havoid base (or_introl eq_refl) Hrel).
    + rewrite IH. split.
      * intros Htail element [<-|Hin].
        -- exact Hrel.
        -- now apply Htail.
      * intro Hall. intros element Hin.
        apply Hall. now right.
Qed.

Definition escaping_code (basis : list {value : X | P value})
    (code : nat) : Prop :=
  match enumerate code with
  | Some candidate => avoids basis candidate
  | None => False
  end.

Definition escaping_code_dec (basis : list {value : X | P value})
    (code : nat) : {escaping_code basis code} + {~ escaping_code basis code}.
Proof.
  unfold escaping_code. destruct (enumerate code) as [candidate|] eqn:Hdecode.
  - destruct (avoidsb basis candidate) eqn:Havoid.
    + left. now apply avoidsb_true_iff.
    + right. intro H. apply avoidsb_true_iff in H. congruence.
  - right. tauto.
Defined.

Hypothesis enumerate_sound : forall code value,
  enumerate code = Some value -> P value.
Hypothesis enumerate_complete : forall value, P value ->
  exists code, enumerate code = Some value.

Theorem countable_af_finite_cover :
    afs P R -> exists basis : list {value : X | P value},
      forall value : {value : X | P value},
        exists base, List.In base basis /\
          R (proj1_sig base) (proj1_sig value).
Proof.
  intro Haf.
  destruct (classic (exists basis : list {value : X | P value},
      forall value : {value : X | P value},
        exists base, List.In base basis /\
          R (proj1_sig base) (proj1_sig value)))
    as [Hcover|Hno]; [exact Hcover|].
  exfalso.
  assert (Hescape : forall basis : list {value : X | P value},
      exists value, P value /\ avoids basis value).
  { intro basis. apply NNPP. intro Hnone. apply Hno. exists basis.
    intros [value Hvalid]. apply NNPP. intro Hnotcovered. apply Hnone.
    exists value. split; [exact Hvalid|].
    intros base Hin Hrel. apply Hnotcovered. exists base. auto. }
  assert (Hescaping_code : forall basis : list {value : X | P value},
      exists code, escaping_code basis code).
  { intro basis. destruct (Hescape basis) as [value [Hvalid Hvalue]].
    destruct (enumerate_complete value Hvalid) as [code Hcode].
    exists code. unfold escaping_code. now rewrite Hcode. }
  assert (choose_escape : forall basis : list {value : X | P value},
      {value : X | P value /\ avoids basis value}).
  { intro basis.
    destruct (@constructive_indefinite_ground_description_nat
      (escaping_code basis) (escaping_code_dec basis)
      (Hescaping_code basis)) as [code Hcode].
    unfold escaping_code in Hcode.
    destruct (enumerate code) as [value|] eqn:Hdecode; [|contradiction].
    exists value. split; [eapply enumerate_sound; eauto|exact Hcode]. }
  set (build := fix build (count : nat) : list {value : X | P value} :=
    match count with
    | O => []
    | S count' =>
        let prefix := build count' in
        prefix ++ [exist _ (proj1_sig (choose_escape prefix))
          (proj1 (proj2_sig (choose_escape prefix)))]
    end).
  set (bad := fun index =>
    exist P (proj1_sig (choose_escape (build index)))
      (proj1 (proj2_sig (choose_escape (build index))))).
  assert (Hbuild_succ : forall index,
      build (S index) = build index ++ [bad index]).
  { intro index. unfold bad. cbn. reflexivity. }
  assert (Hbuild_prefix : forall earlier later, earlier <= later ->
      exists suffix, build later = build earlier ++ suffix).
  { intros earlier later Hle. induction Hle.
    - exists []. now rewrite app_nil_r.
    - destruct IHHle as [suffix Hsuffix].
      rewrite Hbuild_succ, Hsuffix.
      exists (suffix ++ [bad m]). symmetry. apply app_assoc. }
  assert (Hbad_member : forall earlier later, earlier < later ->
      List.In (bad earlier) (build later)).
  { intros earlier later Hlt.
    destruct (Hbuild_prefix (S earlier) later ltac:(lia)) as [suffix Hsuffix].
    rewrite Hsuffix, Hbuild_succ, in_app_iff. left.
    apply in_app_iff. right. cbn. auto. }
  pose proof (@afs_af_sub_rel X P R Haf) as Haf_sig.
  destruct (@af_recursion {value : X | P value}
      (fun left right => R (proj1_sig left) (proj1_sig right))
      Haf_sig bad) as [bound [earlier [later [[Hlt _] Hrel]]]].
  exact ((proj2 (proj2_sig (choose_escape (build later))))
    (bad earlier) (Hbad_member earlier later Hlt) Hrel).
Qed.

End CountableFiniteBasis.

Arguments countable_af_finite_cover {X} enumerate P R R_dec
  enumerate_sound enumerate_complete _.
