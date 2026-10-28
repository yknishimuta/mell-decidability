From Coq Require Import List Vector VectorSpec ZArith Lia Classical_Prop.
From KruskalAfProp Require Import af.af af.af_tools af.af_ramsey.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Periodic.
From Mell.BVAS Require Import RunOrder.
From Mell.Order Require Import AlmostFullBridge.

Import ListNotations.
Open Scope Z_scope.

Definition ZSet (d : nat) := ZVec d -> Prop.

Definition zvec_sub {d} (left right : ZVec d) : ZVec d :=
  Vector.map2 Z.sub left right.

Fixpoint zvec_linear_combination {d} (generators : list (ZVec d))
    (coefficients : list nat) : ZVec d :=
  match generators, coefficients with
  | generator :: generators', coefficient :: coefficients' =>
      zvec_add (zvec_nsmul coefficient generator)
        (zvec_linear_combination generators' coefficients')
  | _, _ => zvec_zero d
  end.

Definition zvec_generated {d} (generators : list (ZVec d))
    (value : ZVec d) : Prop :=
  exists coefficients : NVec (length generators),
    zvec_linear_combination generators (Vector.to_list coefficients) = value.

Definition PeriodicLe {d} (P : ZSet d) (x y : ZVec d) : Prop :=
  P (zvec_sub y x).

Definition FinitelyGeneratedPeriodic {d} (P : ZSet d) : Prop :=
  exists generators : list (ZVec d),
    (forall g, List.In g generators -> P g) /\
    forall x, P x <-> zvec_generated generators x.

Lemma zvec_ext : forall d (x y : ZVec d),
    (forall i, Vector.nth x i = Vector.nth y i) -> x = y.
Proof.
  intros d x y H. apply (proj1 (Vector.eq_nth_iff Z d x y)).
  intros i j ->. apply H.
Qed.
Lemma zvec_add_zero_right : forall d (x : ZVec d),
    zvec_add x (zvec_zero d) = x.
Proof.
  intros d x. apply zvec_ext. intro i. unfold zvec_add, zvec_zero.
  rewrite (nth_map2 Z.add x (Vector.const 0 d) i i i eq_refl eq_refl),
    (const_nth Z 0 d i). lia.
Qed.

Lemma zvec_add_zero_left : forall d (x : ZVec d),
    zvec_add (zvec_zero d) x = x.
Proof.
  intros d x. apply zvec_ext. intro i. unfold zvec_add, zvec_zero.
  rewrite (nth_map2 Z.add (Vector.const 0 d) x i i i eq_refl eq_refl),
    (const_nth Z 0 d i). lia.
Qed.

Lemma zvec_add_assoc : forall d (x y z : ZVec d),
    zvec_add (zvec_add x y) z = zvec_add x (zvec_add y z).
Proof.
  intros d x y z. apply zvec_ext. intro i. unfold zvec_add.
  repeat rewrite (nth_map2 Z.add _ _ i i i eq_refl eq_refl). lia.
Qed.

Lemma zvec_add_comm : forall d (x y : ZVec d), zvec_add x y = zvec_add y x.
Proof.
  intros d x y. apply zvec_ext. intro i. unfold zvec_add.
  repeat rewrite (nth_map2 Z.add _ _ i i i eq_refl eq_refl). lia.
Qed.

Lemma zvec_sub_add_cancel : forall d (x y : ZVec d),
    zvec_add x (zvec_sub y x) = y.
Proof.
  intros d x y. apply zvec_ext. intro i. unfold zvec_add, zvec_sub.
  repeat rewrite (nth_map2 _ _ _ i i i eq_refl eq_refl). lia.
Qed.

Lemma zvec_sub_add : forall d (x y z : ZVec d),
    zvec_sub (zvec_add y z) (zvec_add x z) = zvec_sub y x.
Proof.
  intros d x y z. apply zvec_ext. intro i. unfold zvec_add, zvec_sub.
  repeat rewrite (nth_map2 _ _ _ i i i eq_refl eq_refl). lia.
Qed.

Lemma zvec_nsmul_add : forall d a b (x : ZVec d),
    zvec_nsmul (a + b) x = zvec_add (zvec_nsmul a x) (zvec_nsmul b x).
Proof.
  intros d a. induction a as [|a IH]; intros b x; cbn.
  - rewrite zvec_add_comm. symmetry. apply zvec_add_zero_right.
  - rewrite IH. symmetry. apply zvec_add_assoc.
Qed.

Lemma linear_combination_app : forall d (gs hs : list (ZVec d)) cs ds,
    length cs = length gs -> length ds = length hs ->
    zvec_linear_combination (gs ++ hs) (cs ++ ds) =
      zvec_add (zvec_linear_combination gs cs)
        (zvec_linear_combination hs ds).
Proof.
  intros d gs. induction gs as [|g gs IH]; intros hs cs ds Hcs Hds.
  - destruct cs; [cbn; now rewrite zvec_add_comm, zvec_add_zero_right|discriminate].
  - destruct cs as [|c cs]; [discriminate|]. cbn in Hcs |- *.
    rewrite IH by auto. symmetry. apply zvec_add_assoc.
Qed.

Lemma linear_combination_zeros : forall d gs,
    zvec_linear_combination gs (repeat 0%nat (length gs)) = zvec_zero d.
Proof.
  intros d gs. induction gs as [|g gs IH]; cbn; [reflexivity|].
  rewrite IH, zvec_add_zero_right. reflexivity.
Qed.

Lemma generated_zero : forall d gs, zvec_generated gs (zvec_zero d).
Proof.
  intros d gs. exists (Vector.const 0%nat (length gs)).
  rewrite to_list_const. apply linear_combination_zeros.
Qed.

Lemma generated_generator : forall d gs (g : ZVec d), List.In g gs ->
    zvec_generated gs g.
Proof.
  intros d gs. induction gs as [|h gs IH]; intros g Hin; [contradiction|].
  destruct Hin as [<-|Hin].
  - destruct (generated_zero d gs) as [cs Hcs].
    exists (@Vector.cons nat 1%nat _ cs).
    change (zvec_add (zvec_nsmul 1 h)
      (zvec_linear_combination gs (Vector.to_list cs)) = h).
    rewrite Hcs. cbn.
    repeat rewrite zvec_add_zero_right. reflexivity.
  - destruct (IH g Hin) as [cs Hsum].
    exists (@Vector.cons nat 0%nat _ cs).
    change (zvec_add (zvec_nsmul 0 h)
      (zvec_linear_combination gs (Vector.to_list cs)) = g).
    cbn. rewrite zvec_add_zero_left. exact Hsum.
Qed.

Lemma linear_combination_vector_add : forall d (gs : list (ZVec d))
    (cs ds : NVec (length gs)),
    zvec_linear_combination gs
      (Vector.to_list (Vector.map2 Nat.add cs ds)) =
    zvec_add (zvec_linear_combination gs (Vector.to_list cs))
      (zvec_linear_combination gs (Vector.to_list ds)).
Proof.
  intros d gs. induction gs as [|g gs IH]; intros cs ds.
  - refine (Vector.case0 (fun cs =>
      zvec_linear_combination []
        (Vector.to_list (Vector.map2 Nat.add cs ds)) =
      zvec_add (zvec_linear_combination [] (Vector.to_list cs))
        (zvec_linear_combination [] (Vector.to_list ds))) _ cs).
    refine (Vector.case0 (fun ds =>
      zvec_linear_combination []
        (Vector.to_list (Vector.map2 Nat.add (@Vector.nil nat) ds)) =
      zvec_add
        (zvec_linear_combination [] (Vector.to_list (@Vector.nil nat)))
        (zvec_linear_combination [] (Vector.to_list ds))) _ ds).
    cbn. now rewrite zvec_add_zero_right.
  - refine (Vector.caseS' cs (fun cs =>
      zvec_linear_combination (g :: gs)
        (Vector.to_list (Vector.map2 Nat.add cs ds)) =
      zvec_add (zvec_linear_combination (g :: gs) (Vector.to_list cs))
        (zvec_linear_combination (g :: gs) (Vector.to_list ds))) _).
    intros c cs'.
    refine (Vector.caseS' ds (fun ds =>
      zvec_linear_combination (g :: gs)
        (Vector.to_list (Vector.map2 Nat.add
          (@Vector.cons nat c _ cs') ds)) =
      zvec_add
        (zvec_linear_combination (g :: gs)
          (Vector.to_list (@Vector.cons nat c _ cs')))
        (zvec_linear_combination (g :: gs) (Vector.to_list ds))) _).
    intros e ds'. cbn.
    change (zvec_add (zvec_nsmul (c + e)%nat g)
      (zvec_linear_combination gs
        (Vector.to_list (Vector.map2 Nat.add cs' ds'))) =
      zvec_add
        (zvec_add (zvec_nsmul c g)
          (zvec_linear_combination gs (Vector.to_list cs')))
        (zvec_add (zvec_nsmul e g)
          (zvec_linear_combination gs (Vector.to_list ds')))).
    rewrite zvec_nsmul_add, IH.
      repeat rewrite <- zvec_add_assoc.
      f_equal. rewrite zvec_add_assoc,
        (zvec_add_comm d (zvec_nsmul e g)), <- zvec_add_assoc.
      reflexivity.
Qed.

Lemma generated_add : forall d gs (x y : ZVec d),
    zvec_generated gs x -> zvec_generated gs y ->
    zvec_generated gs (zvec_add x y).
Proof.
  intros d gs x y [cs <-] [ds <-].
  exists (Vector.map2 Nat.add cs ds).
  apply linear_combination_vector_add.
Qed.

Definition nvec_sub_local {d} (upper lower : NVec d) : NVec d :=
  Vector.map2 Nat.sub upper lower.

Lemma nvec_sub_exact_local : forall d (lower upper : NVec d),
    nvec_le lower upper ->
    upper = nvec_add lower (nvec_sub_local upper lower).
Proof.
  intros d lower upper Hle. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros i j Heq. subst j. unfold nvec_add, nvec_sub_local.
  repeat rewrite (nth_map2 _ _ _ i i i eq_refl eq_refl).
  specialize (Hle i). lia.
Qed.

Lemma linear_combination_sub : forall d (gs : list (ZVec d))
    (lower upper : NVec (length gs)), nvec_le lower upper ->
    zvec_sub (zvec_linear_combination gs (Vector.to_list upper))
      (zvec_linear_combination gs (Vector.to_list lower)) =
    zvec_linear_combination gs
      (Vector.to_list (nvec_sub_local upper lower)).
Proof.
  intros d gs lower upper Hle.
  set (delta := nvec_sub_local upper lower).
  assert (Hupper : upper = nvec_add lower delta).
  { unfold delta. apply nvec_sub_exact_local. exact Hle. }
  assert (Heval : zvec_linear_combination gs (Vector.to_list upper) =
      zvec_add (zvec_linear_combination gs (Vector.to_list lower))
        (zvec_linear_combination gs (Vector.to_list delta))).
  { rewrite Hupper. unfold nvec_add. apply linear_combination_vector_add. }
  rewrite Heval. unfold delta.
  apply zvec_ext. intro i. unfold zvec_sub, zvec_add.
  repeat rewrite (nth_map2 _ _ _ i i i eq_refl eq_refl). lia.
Qed.

Theorem finitely_generated_periodic_wqo : forall d (P : ZSet d),
    FinitelyGeneratedPeriodic P -> @afs (ZVec d) P (PeriodicLe P).
Proof.
  intros d P [gs [Hgens Hrepr]].
  eapply afs_rel_morph with
    (f := fun coefficients value =>
      zvec_linear_combination gs (Vector.to_list coefficients) = value)
    (P := fun _ : NVec (length gs) => True)
    (R := @nvec_le (length gs)).
  - intros value Hvalue.
    destruct (proj1 (Hrepr value) Hvalue) as [coefficients Heval].
    exists coefficients. auto.
  - intros left right x y _ _ Hx Hy Hleft Hright Hle.
    subst x y. unfold PeriodicLe.
    apply (proj2 (Hrepr _)).
    exists (nvec_sub_local right left).
    symmetry. apply linear_combination_sub. exact Hle.
  - apply af_iff_afs_True. apply nvec_le_almost_full.
Qed.

Definition SignVec (d : nat) := Vec bool d.

Definition sign_apply {d} (sign : SignVec d) (value : ZVec d) : ZVec d :=
  Vector.map2 (fun (positive : bool) (coordinate : Z) =>
    if positive then coordinate else (- coordinate)%Z) sign value.

Definition sign_decode {d} (sign : SignVec d) (value : NVec d) : ZVec d :=
  sign_apply sign (nvec_to_zvec value).

Definition OrthantPart {d} (P : ZSet d) (sign : SignVec d)
    (value : NVec d) : Prop := P (sign_decode sign value).

Lemma sign_apply_involutive : forall d (sign : SignVec d) value,
    sign_apply sign (sign_apply sign value) = value.
Proof.
  intros d sign value. apply zvec_ext. intro i. unfold sign_apply.
  repeat rewrite (nth_map2 _ _ _ i i i eq_refl eq_refl).
  destruct (Vector.nth sign i); cbn; lia.
Qed.

Lemma sign_apply_add : forall d (sign : SignVec d) left right,
    sign_apply sign (zvec_add left right) =
    zvec_add (sign_apply sign left) (sign_apply sign right).
Proof.
  intros d sign left right. apply zvec_ext. intro i.
  unfold sign_apply, zvec_add.
  repeat rewrite (nth_map2 _ _ _ i i i eq_refl eq_refl).
  destruct (Vector.nth sign i); cbn; lia.
Qed.

Lemma sign_decode_zero : forall d (sign : SignVec d),
    sign_decode sign (nvec_zero d) = zvec_zero d.
Proof.
  intros d sign. apply zvec_ext. intro i.
  unfold sign_decode, sign_apply, nvec_to_zvec, nvec_zero, zvec_zero.
  rewrite (nth_map2 _ _ _ i i i eq_refl eq_refl),
    (nth_map _ _ i i eq_refl), !const_nth.
  destruct (Vector.nth sign i); reflexivity.
Qed.

Lemma sign_decode_add : forall d (sign : SignVec d) left right,
    sign_decode sign (nvec_add left right) =
    zvec_add (sign_decode sign left) (sign_decode sign right).
Proof.
  intros d sign left right. apply zvec_ext. intro i.
  unfold sign_decode, sign_apply, nvec_to_zvec, nvec_add, zvec_add.
  repeat rewrite (nth_map2 _ _ _ i i i eq_refl eq_refl).
  repeat rewrite (nth_map _ _ i i eq_refl).
  repeat rewrite (nth_map2 _ _ _ i i i eq_refl eq_refl).
  rewrite Nat2Z.inj_add. destruct (Vector.nth sign i); cbn; lia.
Qed.

Lemma sign_decode_sub : forall d (sign : SignVec d) lower upper,
    nvec_le lower upper ->
    zvec_sub (sign_decode sign upper) (sign_decode sign lower) =
    sign_decode sign (nvec_sub_local upper lower).
Proof.
  intros d sign lower upper Hle. apply zvec_ext. intro i.
  unfold sign_decode, sign_apply, nvec_to_zvec, nvec_sub_local, zvec_sub.
  repeat rewrite (nth_map2 _ _ _ i i i eq_refl eq_refl).
  repeat rewrite (nth_map _ _ i i eq_refl).
  repeat rewrite (nth_map2 _ _ _ i i i eq_refl eq_refl).
  specialize (Hle i). destruct (Vector.nth sign i); cbn.
  - rewrite Nat2Z.inj_sub by exact Hle. lia.
  - rewrite Nat2Z.inj_sub by exact Hle. lia.
Qed.

Lemma orthant_part_periodic : forall d (P : ZSet d) sign,
    Periodic P ->
    OrthantPart P sign (nvec_zero d) /\
    forall left right, OrthantPart P sign left ->
      OrthantPart P sign right ->
      OrthantPart P sign (nvec_add left right).
Proof.
  intros d P sign [Hzero Hadd]. split.
  - unfold OrthantPart. rewrite sign_decode_zero. exact Hzero.
  - intros left right Hleft Hright. unfold OrthantPart in *.
    rewrite sign_decode_add. now apply Hadd.
Qed.

Definition OrthantLe {d} (P : ZSet d) (sign : SignVec d)
    (left right : NVec d) : Prop :=
  nvec_le left right /\
  OrthantPart P sign (nvec_sub_local right left).

Lemma orthant_le_iff : forall d (P : ZSet d) sign left right,
    nvec_le left right ->
    (PeriodicLe P (sign_decode sign left) (sign_decode sign right) <->
     OrthantPart P sign (nvec_sub_local right left)).
Proof.
  intros d P sign left right Hle. unfold PeriodicLe, OrthantPart.
  now rewrite sign_decode_sub by exact Hle.
Qed.

Lemma orthant_transport_wqo : forall d (P : ZSet d) sign,
    @afs (ZVec d) P (PeriodicLe P) ->
    @afs (NVec d) (OrthantPart P sign)
      (fun left right =>
        PeriodicLe P (sign_decode sign left) (sign_decode sign right)).
Proof.
  intros d P sign Haf.
  eapply afs_rel_morph with
    (f := fun source target => source = sign_decode sign target)
    (P := P) (R := PeriodicLe P).
  - intros target Htarget. exists (sign_decode sign target). auto.
  - intros source1 source2 target1 target2 _ _ _ _ -> -> Hrel.
    exact Hrel.
  - exact Haf.
Qed.

Theorem orthant_order_wqo : forall d (P : ZSet d) sign,
    @afs (ZVec d) P (PeriodicLe P) ->
    @afs (NVec d) (OrthantPart P sign) (OrthantLe P sign).
Proof.
  intros d P sign Haf.
  pose proof (orthant_transport_wqo d P sign Haf) as Htransport.
  assert (Hcoordinate : @afs (NVec d) (OrthantPart P sign) nvec_le).
  { apply af_sub_rel_afs. apply af_af_sub_rel. apply nvec_le_almost_full. }
  assert (Hboth : @afs (NVec d) (OrthantPart P sign)
      (fun left right =>
        PeriodicLe P (sign_decode sign left) (sign_decode sign right) /\
        nvec_le left right)).
  { apply af_sub_rel_afs.
    exact (af_inter (afs_af_sub_rel Htransport)
      (afs_af_sub_rel Hcoordinate)). }
  eapply afs_mono with (3 := Hboth).
  - firstorder.
  - intros left right Hleft Hright [Hperiodic Hle].
    split; [exact Hle|].
    apply (proj1 (orthant_le_iff d P sign left right Hle)).
    exact Hperiodic.
Qed.

Fixpoint nvec_norm {d} (value : NVec d) : nat :=
  match value with
  | Vector.nil => 0%nat
  | Vector.cons head tail => head + nvec_norm tail
  end.

Lemma nvec_norm_eq_zero : forall d (value : NVec d),
    nvec_norm value = 0%nat -> value = nvec_zero d.
Proof.
  intros d value. induction value as [|head d tail IH]; intro H; [reflexivity|].
  cbn in H. assert (head = 0%nat /\ nvec_norm tail = 0%nat) by lia.
  destruct H0 as [-> Htail]. rewrite (IH Htail). reflexivity.
Qed.

Lemma nvec_norm_positive : forall d (value : NVec d),
    value <> nvec_zero d -> (0 < nvec_norm value)%nat.
Proof.
  intros d value H. destruct (nvec_norm value) eqn:Hnorm; [|lia].
  exfalso. apply H. now apply nvec_norm_eq_zero.
Qed.

Lemma nvec_norm_add : forall d (left right : NVec d),
    nvec_norm (nvec_add left right) =
      (nvec_norm left + nvec_norm right)%nat.
Proof.
  intros d left. induction left as [|head d tail IH]; intro right.
  - refine (Vector.case0 (fun right =>
      nvec_norm (nvec_add (@Vector.nil nat) right) =
      (nvec_norm (@Vector.nil nat) + nvec_norm right)%nat) _ right). reflexivity.
  - refine (Vector.caseS' right (fun right =>
      nvec_norm (nvec_add (@Vector.cons nat head d tail) right) =
      (nvec_norm (@Vector.cons nat head d tail) + nvec_norm right)%nat) _).
    intros other rest. cbn. rewrite IH. lia.
Qed.

Lemma generated_append_left : forall d (left right : list (ZVec d)) value,
    zvec_generated left value -> zvec_generated (left ++ right) value.
Proof.
  intros d left right value [coeff Hcoeff].
  unfold zvec_generated. rewrite app_length.
  exists (Vector.append coeff (Vector.const 0%nat (length right))).
  rewrite to_list_append, to_list_const, linear_combination_app;
    [|now rewrite length_to_list|now rewrite repeat_length].
  rewrite linear_combination_zeros, zvec_add_zero_right. exact Hcoeff.
Qed.

Lemma generated_append_right : forall d (left right : list (ZVec d)) value,
    zvec_generated right value -> zvec_generated (left ++ right) value.
Proof.
  intros d left right value [coeff Hcoeff].
  unfold zvec_generated. rewrite app_length.
  exists (Vector.append (Vector.const 0%nat (length left)) coeff).
  rewrite to_list_append, to_list_const, linear_combination_app;
    [|now rewrite repeat_length|now rewrite length_to_list].
  rewrite linear_combination_zeros, zvec_add_zero_left. exact Hcoeff.
Qed.

Lemma af_finite_cover_classic : forall X (R : X -> X -> Prop),
    af R -> exists basis : list X,
      forall x, exists b, List.In b basis /\ R b x.
Proof.
  intros X R Haf.
  assert (Hacc : forall (T : X -> X -> Prop), af T ->
      forall prefix : list X,
        (forall u v, T u v ->
          R u v \/ exists b, List.In b prefix /\ R b u) ->
        exists basis : list X,
          forall x, exists b, List.In b basis /\ R b x).
  { intros T HT. induction HT as [T Hfull|T Hlift IH].
    - intros prefix Hshape.
      destruct (classic (forall x, exists b, List.In b prefix /\ R b x))
        as [Hcovered|Hnot]; [now exists prefix|].
      assert (Hescape : exists x, forall b, List.In b prefix -> ~ R b x).
      { apply NNPP. intro Hnone. apply Hnot. intro x. apply NNPP. intro Hx.
        apply Hnone. exists x. intros b Hb Hrel. apply Hx. now exists b. }
      destruct Hescape as [x Hx]. exists (x :: prefix). intro y.
      exists x. split; [now left|].
      destruct (Hshape x y (Hfull x y)) as [Hxy|[b [Hb Hbx]]];
        [exact Hxy|exfalso; exact (Hx b Hb Hbx)].
    - intros prefix Hshape.
      destruct (classic (forall x, exists b, List.In b prefix /\ R b x))
        as [Hcovered|Hnot]; [now exists prefix|].
      assert (Hescape : exists x, forall b, List.In b prefix -> ~ R b x).
      { apply NNPP. intro Hnone. apply Hnot. intro x. apply NNPP. intro Hx.
        apply Hnone. exists x. intros b Hb Hrel. apply Hx. now exists b. }
      destruct Hescape as [x Hx]. apply (IH x (x :: prefix)).
      intros u v [Huv|Hxu].
      + destruct (Hshape u v Huv) as [Huv'|[b [Hb Hbu]]].
        * now left.
        * right. exists b. split; [now right|exact Hbu].
      + destruct (Hshape x u Hxu) as [Hxu'|[b [Hb Hbx]]].
        * right. exists x. split; [now left|exact Hxu'].
        * exfalso. exact (Hx b Hb Hbx). }
  apply (Hacc R Haf []). intros u v Huv. now left.
Qed.

Lemma restricted_af_finite_cover_classic : forall X (P : X -> Prop)
    (R : X -> X -> Prop),
    afs P R -> exists basis : list {x : X | P x},
      forall x : {x : X | P x},
        exists b, List.In b basis /\ R (proj1_sig b) (proj1_sig x).
Proof.
  intros X P R Hafs. apply af_finite_cover_classic.
  exact (@afs_af_sub_rel X P R Hafs).
Qed.

Theorem orthant_finite_generators : forall d (P : ZSet d) sign,
    Periodic P -> @afs (ZVec d) P (PeriodicLe P) ->
    exists generators : list (ZVec d),
      (forall generator, List.In generator generators -> P generator) /\
      forall value, OrthantPart P sign value ->
        zvec_generated generators (sign_decode sign value).
Proof.
  intros d P sign Hperiodic Haf.
  pose proof (orthant_order_wqo d P sign Haf) as Horthant.
  assert (Hnonzero : @afs (NVec d)
      (fun value => OrthantPart P sign value /\ value <> nvec_zero d)
      (OrthantLe P sign)).
  { eapply afs_mono with (3 := Horthant); firstorder. }
  destruct (restricted_af_finite_cover_classic _ _ _ Hnonzero)
    as [basis Hcover].
  set (generators := List.map
    (fun base => sign_decode sign (proj1_sig base)) basis).
  exists generators. split.
  - intros generator Hin. unfold generators in Hin.
    apply in_map_iff in Hin. destruct Hin as [base [<- Hin]].
    exact (proj1 (proj2_sig base)).
  - intros value Hvalue.
    assert (Hbounded : forall (bound : nat) (candidate : NVec d),
        (nvec_norm candidate < bound)%nat -> OrthantPart P sign candidate ->
        zvec_generated generators (sign_decode sign candidate)).
    { intro bound. induction bound as [|bound IH];
        intros candidate Hnorm Hcandidate; [lia|].
      destruct (nvec_eq_dec candidate (nvec_zero d)) as [->|Hcandidate_nz].
      - rewrite sign_decode_zero. apply generated_zero.
      - destruct (Hcover (exist _ candidate (conj Hcandidate Hcandidate_nz)))
          as [base [Hbase Hinorder]].
        destruct Hinorder as [Hle Hremainder].
        set (remainder := nvec_sub_local candidate (proj1_sig base)).
        assert (Hcandidate_eq : candidate =
            nvec_add (proj1_sig base) remainder).
        { unfold remainder. apply nvec_sub_exact_local. exact Hle. }
        assert (Hremainder_norm : (nvec_norm remainder < bound)%nat).
        { rewrite Hcandidate_eq, nvec_norm_add in Hnorm.
          pose proof (nvec_norm_positive d (proj1_sig base)
            (proj2 (proj2_sig base))). lia. }
        rewrite Hcandidate_eq, sign_decode_add. apply generated_add.
        + apply generated_generator. unfold generators.
          apply in_map_iff. exists base. split; [reflexivity|exact Hbase].
        + apply IH; [exact Hremainder_norm|].
          unfold remainder. exact Hremainder. }
    apply (Hbounded (S (nvec_norm value)) value); [lia|exact Hvalue].
Qed.

Fixpoint all_signs (d : nat) : list (SignVec d) :=
  match d with
  | O => [@Vector.nil bool]
  | S d' =>
      List.map (fun tail => @Vector.cons bool true d' tail) (all_signs d') ++
      List.map (fun tail => @Vector.cons bool false d' tail) (all_signs d')
  end.

Lemma all_signs_complete : forall d (sign : SignVec d),
    List.In sign (all_signs d).
Proof.
  intros d sign. induction sign as [|head d tail IH]; cbn; [auto|].
  apply in_app_iff. destruct head.
  - left. apply in_map_iff. exists tail. auto.
  - right. apply in_map_iff. exists tail. auto.
Qed.

Definition sign_of_zvec {d} (value : ZVec d) : SignVec d :=
  Vector.map (fun coordinate => Z.leb 0 coordinate) value.

Definition magnitude_zvec {d} (value : ZVec d) : NVec d :=
  Vector.map (fun coordinate => Z.to_nat (Z.abs coordinate)) value.

Lemma sign_magnitude_decode : forall d (value : ZVec d),
    sign_decode (sign_of_zvec value) (magnitude_zvec value) = value.
Proof.
  intros d value. apply zvec_ext. intro i.
  unfold sign_decode, sign_apply, sign_of_zvec, magnitude_zvec, nvec_to_zvec.
  repeat rewrite (nth_map2 _ _ _ i i i eq_refl eq_refl).
  repeat rewrite (nth_map _ _ i i eq_refl).
  destruct (Z.leb_spec0 0 (Vector.nth value i)) as [Hnonnegative|Hnegative].
  - rewrite Z.abs_eq by lia. rewrite Z2Nat.id by lia. reflexivity.
  - rewrite Z.abs_neq by lia. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma generated_in_periodic : forall d (P : ZSet d) generators value,
    Periodic P ->
    (forall generator, List.In generator generators -> P generator) ->
    zvec_generated generators value -> P value.
Proof.
  intros d P generators value Hperiodic Hgenerators [coefficients <-].
  revert coefficients Hgenerators.
  induction generators as [|generator generators IH]; intros coefficients Hall.
  - refine (Vector.case0 (fun coefficients =>
      P (zvec_linear_combination [] (Vector.to_list coefficients)))
      _ coefficients). cbn. exact (proj1 Hperiodic).
  - refine (Vector.caseS' coefficients (fun coefficients =>
      P (zvec_linear_combination (generator :: generators)
        (Vector.to_list coefficients))) _).
    intros coefficient coefficients'.
    change (P (zvec_add (zvec_nsmul coefficient generator)
      (zvec_linear_combination generators (Vector.to_list coefficients')))).
    apply (proj2 Hperiodic).
    + apply periodic_nsmul with (set := P); [exact Hperiodic|].
      apply Hall. now left.
    + apply IH. intros g Hin. apply Hall. now right.
Qed.

Lemma finite_sign_generators : forall d (P : ZSet d) signs,
    Periodic P -> @afs (ZVec d) P (PeriodicLe P) ->
    exists generators : list (ZVec d),
      (forall generator, List.In generator generators -> P generator) /\
      forall sign value, List.In sign signs -> OrthantPart P sign value ->
        zvec_generated generators (sign_decode sign value).
Proof.
  intros d P signs. induction signs as [|sign signs IH]; intros Hperiodic Haf.
  - exists []. split; [intros g Hin; contradiction|].
    intros s value Hin. contradiction.
  - destruct (orthant_finite_generators d P sign Hperiodic Haf)
      as [head_generators [Hhead_generators Hhead]].
    destruct (IH Hperiodic Haf)
      as [tail_generators [Htail_generators Htail]].
    exists (head_generators ++ tail_generators). split.
    + intros generator Hin. apply in_app_iff in Hin. destruct Hin;
        [now apply Hhead_generators|now apply Htail_generators].
    + intros current value [<-|Hin] Hvalue.
      * apply generated_append_left. now apply Hhead.
      * apply generated_append_right. now apply Htail with (sign := current).
Qed.

Theorem periodic_order_wqo_finitely_generated : forall d (P : ZSet d),
    Periodic P -> @afs (ZVec d) P (PeriodicLe P) ->
    FinitelyGeneratedPeriodic P.
Proof.
  intros d P Hperiodic Haf.
  destruct (finite_sign_generators d P (all_signs d) Hperiodic Haf)
    as [generators [Hgenerators Hall]].
  exists generators. split; [exact Hgenerators|]. intro value. split.
  - intro Hvalue.
    set (sign := sign_of_zvec value).
    set (magnitude := magnitude_zvec value).
    assert (Hpart : OrthantPart P sign magnitude).
    { unfold OrthantPart, sign, magnitude. rewrite sign_magnitude_decode.
      exact Hvalue. }
    specialize (Hall sign magnitude (all_signs_complete d sign) Hpart).
    unfold sign, magnitude in Hall. now rewrite sign_magnitude_decode in Hall.
  - apply generated_in_periodic; assumption.
Qed.

Theorem periodic_order_wqo_iff_finitely_generated : forall d (P : ZSet d),
    Periodic P ->
    (@KruskalAfProp.af.af.afs (ZVec d) P (PeriodicLe P) <->
     FinitelyGeneratedPeriodic P).
Proof.
  intros d P Hperiodic. split.
  - apply periodic_order_wqo_finitely_generated. exact Hperiodic.
  - apply finitely_generated_periodic_wqo.
Qed.




Lemma generated_periodic : forall d gs, Periodic (@zvec_generated d gs).
Proof. intros d gs. split; [apply generated_zero|intros; eapply generated_add; eauto]. Qed.

Lemma finitely_generated_periodic_is_periodic : forall d (P : ZSet d),
    FinitelyGeneratedPeriodic P -> Periodic P.
Proof.
  intros d P [gs [_ H]]. split.
  - apply (proj2 (H _)), generated_zero.
  - intros x y Hx Hy. apply (proj2 (H _)). apply generated_add;
      apply (proj1 (H _)); assumption.
Qed.
