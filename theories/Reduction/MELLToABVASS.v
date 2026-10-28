From Coq Require Import List Vector ZArith Bool Lia Sorting.Permutation.
Require Import Yalla.OLlibs.PermutationPropify.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Reduction Require Import FullZeroSystem ILZ MELLToABVASSRuntime.
Export FullZeroSystem MELLToABVASSRuntime.

Import ListNotations.
Module IF := Yalla.iformulas.

Lemma ill_ll_permutation : forall context context' conclusion,
  Yalla.ill_cut.ill_ll context conclusion ->
  Coq.Sorting.Permutation.Permutation context context' ->
  Yalla.ill_cut.ill_ll context' conclusion.
Proof.
  intros context context' conclusion pi Hperm.
  eapply Yalla.ill_def.ex_ir; [exact pi|].
  cbn. exact (Permutation_Permutation_Type iformula_eq_dec Hperm).
Defined.

Fixpoint expand_counter_context (subformulas : list IF.iformula) :
    NVec (length subformulas) -> list IF.iformula :=
  match subformulas as formulas return
      NVec (length formulas) -> list IF.iformula with
  | [] => fun _ => []
  | formula :: tail => fun counters =>
      repeat formula (Vector.hd counters) ++
      expand_counter_context tail (Vector.tl counters)
  end.

Fixpoint encode_counter_context (subformulas : list IF.iformula)
    (context : list IF.iformula) : NVec (length subformulas) :=
  match subformulas with
  | [] => Vector.nil nat
  | formula :: tail =>
      Vector.cons nat (List.count_occ iformula_eq_dec context formula)
        _ (encode_counter_context tail context)
  end.

Definition support_context (support : list IF.iformula) : list IF.iformula :=
  List.map IF.ioc support.

Definition machine_context (subformulas support : list IF.iformula)
    (counters : NVec (length subformulas)) : list IF.iformula :=
  support_context support ++ expand_counter_context subformulas counters.

Lemma expand_counter_context_absent : forall subformulas formula
    (counters : NVec (length subformulas)),
  ~ List.In formula subformulas ->
  List.count_occ iformula_eq_dec
    (expand_counter_context subformulas counters) formula = 0.
Proof.
  induction subformulas as [|head tail IH]; intros formula counters Hnotin.
  - refine (Vector.case0 (fun counters =>
      List.count_occ iformula_eq_dec
        (expand_counter_context [] counters) formula = 0) _ counters).
    reflexivity.
  - refine (Vector.caseS' counters (fun counters =>
      List.count_occ iformula_eq_dec
        (expand_counter_context (head :: tail) counters) formula = 0) _).
    intros count rest. cbn.
    assert (Hneq : formula <> head).
    { intro Heq; apply Hnotin; subst; now left. }
    assert (Htail : ~ List.In formula tail).
    { intro Hin; apply Hnotin; now right. }
    rewrite List.count_occ_app,
      List.count_occ_repeat_neq by exact Hneq.
    rewrite IH by exact Htail. lia.
Qed.

Lemma encode_counter_context_repeat_absent : forall subformulas formula count context,
  ~ List.In formula subformulas ->
  encode_counter_context subformulas (repeat formula count ++ context) =
  encode_counter_context subformulas context.
Proof.
  induction subformulas as [|head tail IH]; intros formula count context Hnotin;
    cbn; [reflexivity|].
  f_equal.
  - rewrite List.count_occ_app,
      List.count_occ_repeat_neq; [lia|].
    intro Heq; apply Hnotin; subst; now left.
  - apply IH. intro Hin; apply Hnotin; now right.
Qed.

Lemma encode_expand_counter_context : forall subformulas
    (counters : NVec (length subformulas)),
  NoDup subformulas ->
  encode_counter_context subformulas
    (expand_counter_context subformulas counters) = counters.
Proof.
  induction subformulas as [|head tail IH]; intros counters Hnodup.
  - refine (Vector.case0 (fun counters =>
      encode_counter_context [] (expand_counter_context [] counters) = counters)
      _ counters). reflexivity.
  - refine (Vector.caseS' counters (fun counters =>
      encode_counter_context (head :: tail)
        (expand_counter_context (head :: tail) counters) = counters) _).
    intros count rest. inversion Hnodup as [|? ? Hhead Htail]; subst.
    cbn. f_equal.
    + rewrite List.count_occ_app,
        List.count_occ_repeat_eq by reflexivity.
      rewrite expand_counter_context_absent by exact Hhead. lia.
    + rewrite encode_counter_context_repeat_absent by exact Hhead.
      apply IH. exact Htail.
Qed.

Lemma count_expand_encode_counter_context : forall subformulas context formula,
  NoDup subformulas -> List.In formula subformulas ->
  List.count_occ iformula_eq_dec
    (expand_counter_context subformulas
      (encode_counter_context subformulas context)) formula =
  List.count_occ iformula_eq_dec context formula.
Proof.
  induction subformulas as [|head tail IH]; intros context formula Hnodup Hin.
  - contradiction.
  - inversion Hnodup as [|? ? Hhead Htail]; subst.
    cbn. rewrite List.count_occ_app.
    destruct Hin as [Heq | Hin].
    + subst formula.
      rewrite List.count_occ_repeat_eq by reflexivity.
      rewrite expand_counter_context_absent by exact Hhead. lia.
    + rewrite List.count_occ_repeat_neq.
      * rewrite (IH context formula Htail Hin). reflexivity.
      * intro Heq; subst formula; contradiction.
Qed.

Lemma expand_encode_counter_context_permutation : forall subformulas
    (context : list IF.iformula),
  NoDup subformulas ->
  List.Forall (fun formula => List.In formula subformulas) context ->
  Coq.Sorting.Permutation.Permutation
    (expand_counter_context subformulas
      (encode_counter_context subformulas context)) context.
Proof.
  intros subformulas context Hnodup Hall.
  apply (proj2 (Coq.Sorting.Permutation.Permutation_count_occ
    iformula_eq_dec _ _)).
  intro formula.
  destruct (in_dec iformula_eq_dec formula subformulas) as [Hin | Hnotin].
  - now apply count_expand_encode_counter_context.
  - rewrite expand_counter_context_absent by exact Hnotin.
    symmetry. apply count_occ_not_In.
    intro Hcontext.
    eapply Hnotin.
    rewrite List.Forall_forall in Hall. now apply Hall.
Qed.

Lemma expand_counter_context_forall : forall subformulas
    (counters : NVec (length subformulas)),
  List.Forall (fun formula => List.In formula subformulas)
    (expand_counter_context subformulas counters).
Proof.
  induction subformulas as [|head tail IH]; intros counters.
  - refine (Vector.case0 (fun counters =>
      List.Forall (fun formula => List.In formula [])
        (expand_counter_context [] counters)) _ counters).
    constructor.
  - refine (Vector.caseS' counters (fun counters =>
      List.Forall (fun formula => List.In formula (head :: tail))
        (expand_counter_context (head :: tail) counters)) _).
    intros count rest. cbn. apply List.Forall_app; split.
    + apply List.Forall_forall. intros formula Hin.
      apply repeat_spec in Hin. subst; now left.
    + eapply List.Forall_impl; [|apply IH]. intros formula Hin; now right.
Qed.

Lemma encode_counter_context_cons : forall subformulas formula context,
  encode_counter_context subformulas (formula :: context) =
  nvec_add (encode_counter_context subformulas [formula])
    (encode_counter_context subformulas context).
Proof.
  induction subformulas as [|head tail IH]; intros formula context; cbn.
  - reflexivity.
  - f_equal.
    + destruct (iformula_eq_dec formula head); cbn;
        destruct (iformula_eq_dec head formula); subst; try congruence; lia.
    + apply IH.
Qed.

Lemma encode_counter_context_app : forall subformulas left right,
  encode_counter_context subformulas (left ++ right) =
  nvec_add (encode_counter_context subformulas left)
    (encode_counter_context subformulas right).
Proof.
  induction subformulas as [|head tail IH]; intros left right; cbn.
  - reflexivity.
  - f_equal.
    + rewrite List.count_occ_app. reflexivity.
    + apply IH.
Qed.

Lemma encode_counter_context_permutation : forall subformulas left right,
  Permutation left right ->
  encode_counter_context subformulas left =
  encode_counter_context subformulas right.
Proof.
  intros subformulas left right Hperm.
  induction subformulas as [|head tail IH]; cbn.
  - reflexivity.
  - f_equal.
    + now apply (proj1 (Permutation_count_occ iformula_eq_dec left right)).
    + apply IH.
Qed.

Lemma encode_counter_context_expand : forall subformulas
    (counters : NVec (length subformulas)),
  NoDup subformulas ->
  encode_counter_context subformulas
    (expand_counter_context subformulas counters) = counters.
Proof. exact encode_expand_counter_context. Qed.

Lemma expand_counter_context_zero : forall subformulas,
  expand_counter_context subformulas (nvec_zero (length subformulas)) = [].
Proof.
  induction subformulas as [|head tail IH];
    cbn [nvec_zero]; [reflexivity|].
  exact IH.
Qed.

Lemma expand_counter_context_add : forall subformulas
    (left right : NVec (length subformulas)),
  NoDup subformulas ->
  Permutation
    (expand_counter_context subformulas (nvec_add left right))
    (expand_counter_context subformulas left ++
      expand_counter_context subformulas right).
Proof.
  intros subformulas left right Hnodup.
  pose proof (expand_encode_counter_context_permutation subformulas
    (expand_counter_context subformulas (nvec_add left right)) Hnodup)
    as Hleft.
  pose proof (expand_encode_counter_context_permutation subformulas
    (expand_counter_context subformulas left ++
      expand_counter_context subformulas right) Hnodup) as Hright.
  specialize (Hleft (expand_counter_context_forall subformulas _)).
  assert (Hall : List.Forall (fun item => List.In item subformulas)
      (expand_counter_context subformulas left ++
       expand_counter_context subformulas right)).
  { apply List.Forall_app; split; apply expand_counter_context_forall. }
  specialize (Hright Hall).
  rewrite encode_expand_counter_context in Hleft by exact Hnodup.
  rewrite encode_counter_context_app,
    !encode_expand_counter_context in Hright by exact Hnodup.
  eapply Permutation_trans; [symmetry; exact Hleft|exact Hright].
Qed.

Lemma formula_add_encode_singleton : forall subformulas formula,
  formula_add subformulas formula =
  nvec_to_zvec (encode_counter_context subformulas [formula]).
Proof.
  induction subformulas as [|head tail IH]; intro formula; cbn.
  - reflexivity.
  - unfold formula_add, formula_action in *; cbn in *.
    f_equal.
    + destruct (Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec formula head)
        as [Heq | Hneq].
      * subst formula.
        destruct (Mell.Reduction.ILZ.iformula_eq_dec head head)
          as [_ | Hcontra]; [reflexivity | contradiction].
      * destruct (Mell.Reduction.ILZ.iformula_eq_dec formula head)
          as [Heq | _]; [contradiction | reflexivity].
    + exact (IH formula).
Qed.

Lemma formula_remove_encode_singleton : forall subformulas formula,
  formula_remove subformulas formula =
  Vector.map Z.opp
    (nvec_to_zvec (encode_counter_context subformulas [formula])).
Proof.
  induction subformulas as [|head tail IH]; intro formula; cbn.
  - reflexivity.
  - unfold formula_remove, formula_action in *; cbn in *.
    f_equal.
    + destruct (Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec formula head)
        as [Heq | Hneq].
      * subst formula.
        destruct (Mell.Reduction.ILZ.iformula_eq_dec head head)
          as [_ | Hcontra]; [reflexivity | contradiction].
      * destruct (Mell.Reduction.ILZ.iformula_eq_dec formula head)
          as [Heq | _]; [contradiction | reflexivity].
    + exact (IH formula).
Qed.

Lemma nvec_sum_singleton_reduction : forall d (value : NVec d),
  nvec_sum [value] = value.
Proof.
  intros d value. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_sum, nvec_add, nvec_zero.
  cbn. rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl),
    (const_nth nat 0 d index). lia.
Qed.

Lemma add_displacement_exact_reduction : forall d (offset : ZVec d)
    children result,
  add_displacement offset children = Some result ->
  zvec_add offset (nvec_to_zvec (nvec_sum children)) =
    nvec_to_zvec result.
Proof.
  intros d offset children result H.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'. unfold nvec_to_zvec.
  rewrite (nth_map Z.of_nat result index index eq_refl).
  eapply zvec_to_nvec_sound; exact H.
Qed.

Lemma add_displacement_of_exact_reduction : forall d (offset : ZVec d)
    children result,
  zvec_add offset (nvec_to_zvec (nvec_sum children)) = nvec_to_zvec result ->
  add_displacement offset children = Some result.
Proof.
  intros d offset children result Hexact. unfold add_displacement.
  rewrite Hexact. apply zvec_to_nvec_of_nvec.
Qed.

Lemma formula_add_displacement : forall subformulas formula source target,
  add_displacement (formula_add subformulas formula) [source] = Some target ->
  target = nvec_add (encode_counter_context subformulas [formula]) source.
Proof.
  intros subformulas formula source target Happly.
  pose proof (add_displacement_exact_reduction _ _ _ _ Happly) as Hexact.
  rewrite nvec_sum_singleton_reduction, formula_add_encode_singleton,
    <- nvec_to_zvec_add in Hexact.
  apply (proj1 (Vector.eq_nth_iff nat _ _ _)).
  intros index index' Heq; subst index'.
  apply (f_equal (fun value => Vector.nth value index)) in Hexact.
  unfold nvec_to_zvec in Hexact.
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl) in Hexact.
  lia.
Qed.

Lemma formula_add_application : forall subformulas formula source,
  add_displacement (formula_add subformulas formula) [source] =
  Some (nvec_add (encode_counter_context subformulas [formula]) source).
Proof.
  intros subformulas formula source. apply add_displacement_of_exact_reduction.
  rewrite nvec_sum_singleton_reduction, formula_add_encode_singleton,
    <- nvec_to_zvec_add. reflexivity.
Qed.

Lemma zvec_zero_add_reduction : forall d (value : ZVec d),
  zvec_add (zvec_zero d) value = value.
Proof.
  intros d value. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'. unfold zvec_add, zvec_zero.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    (const_nth Z 0%Z d index). lia.
Qed.

Lemma zero_displacement_reduction : forall d (source target : NVec d),
  add_displacement (zvec_zero d) [source] = Some target -> target = source.
Proof.
  intros d source target Happly.
  unfold add_displacement in Happly.
  rewrite nvec_sum_singleton_reduction, zvec_zero_add_reduction,
    zvec_to_nvec_of_nvec in Happly.
  now inversion Happly.
Qed.

Lemma zero_displacement_application : forall d (source : NVec d),
  add_displacement (zvec_zero d) [source] = Some source.
Proof.
  intros d source. unfold add_displacement.
  rewrite nvec_sum_singleton_reduction, zvec_zero_add_reduction,
    zvec_to_nvec_of_nvec. reflexivity.
Qed.

Lemma formula_remove_displacement : forall subformulas formula source target,
  add_displacement (formula_remove subformulas formula) [source] = Some target ->
  source = nvec_add (encode_counter_context subformulas [formula]) target.
Proof.
  intros subformulas formula source target Happly.
  pose proof (add_displacement_exact_reduction _ _ _ _ Happly) as Hexact.
  rewrite nvec_sum_singleton_reduction, formula_remove_encode_singleton in Hexact.
  apply (proj1 (Vector.eq_nth_iff nat _ _ _)).
  intros index index' Heq; subst index'.
  apply (f_equal (fun value => Vector.nth value index)) in Hexact.
  unfold nvec_to_zvec, zvec_add, nvec_add in Hexact |- *.
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl) in Hexact.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl) in Hexact.
  rewrite (nth_map Z.opp _ index index eq_refl) in Hexact.
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl) in Hexact.
  rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma formula_remove_application : forall subformulas formula target,
  add_displacement (formula_remove subformulas formula)
    [nvec_add (encode_counter_context subformulas [formula]) target] =
  Some target.
Proof.
  intros subformulas formula target. apply add_displacement_of_exact_reduction.
  rewrite nvec_sum_singleton_reduction, formula_remove_encode_singleton,
    nvec_to_zvec_add.
  apply (proj1 (Vector.eq_nth_iff Z _ _ _)).
  intros index index' Heq; subst index'.
  unfold zvec_add.
  repeat rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl).
  rewrite (nth_map Z.opp _ index index eq_refl). lia.
Qed.

Lemma formula_add_context_permutation : forall subformulas formula source target,
  NoDup subformulas -> List.In formula subformulas ->
  add_displacement (formula_add subformulas formula) [source] = Some target ->
  Coq.Sorting.Permutation.Permutation
    (expand_counter_context subformulas target)
    (formula :: expand_counter_context subformulas source).
Proof.
  intros subformulas formula source target Hnodup Hin Happly.
  pose proof (formula_add_displacement _ _ _ _ Happly) as Htarget.
  pose proof (expand_encode_counter_context_permutation subformulas
    (formula :: expand_counter_context subformulas source) Hnodup) as Hperm.
  assert (Hforall : List.Forall (fun item => List.In item subformulas)
      (formula :: expand_counter_context subformulas source)).
  { constructor; [exact Hin|apply expand_counter_context_forall]. }
  specialize (Hperm Hforall).
  rewrite encode_counter_context_cons,
    encode_expand_counter_context in Hperm by exact Hnodup.
  now rewrite <- Htarget in Hperm.
Qed.

Lemma formula_add_two_displacement : forall subformulas formula source target,
  add_displacement
    (zvec_add (formula_add subformulas formula)
      (formula_add subformulas formula)) [source] = Some target ->
  target = nvec_add (encode_counter_context subformulas [formula])
    (nvec_add (encode_counter_context subformulas [formula]) source).
Proof.
  intros subformulas formula source target Happly.
  pose proof (add_displacement_exact_reduction _ _ _ _ Happly) as Hexact.
  rewrite nvec_sum_singleton_reduction, !formula_add_encode_singleton in Hexact.
  apply (proj1 (Vector.eq_nth_iff nat _ _ _)).
  intros index index' Heq; subst index'.
  apply (f_equal (fun value => Vector.nth value index)) in Hexact.
  unfold zvec_add, nvec_add, nvec_to_zvec in Hexact |- *.
  repeat rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl)
    in Hexact.
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl) in Hexact.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma formula_add_two_context_permutation : forall subformulas formula source target,
  NoDup subformulas -> List.In formula subformulas ->
  add_displacement
    (zvec_add (formula_add subformulas formula)
      (formula_add subformulas formula)) [source] = Some target ->
  Permutation (expand_counter_context subformulas target)
    (formula :: formula :: expand_counter_context subformulas source).
Proof.
  intros subformulas formula source target Hnodup Hin Happly.
  pose proof (formula_add_two_displacement _ _ _ _ Happly) as Htarget.
  rewrite Htarget.
  replace
    (nvec_add (encode_counter_context subformulas [formula])
      (nvec_add (encode_counter_context subformulas [formula]) source))
    with (encode_counter_context subformulas
      (formula :: formula :: expand_counter_context subformulas source)).
  - apply expand_encode_counter_context_permutation; [exact Hnodup|].
    repeat constructor; auto using expand_counter_context_forall.
  - rewrite (encode_counter_context_cons subformulas formula
      (formula :: expand_counter_context subformulas source)).
    rewrite (encode_counter_context_cons subformulas formula
      (expand_counter_context subformulas source)).
    rewrite encode_expand_counter_context by exact Hnodup.
    reflexivity.
Qed.

Lemma formula_remove_context_permutation : forall subformulas formula source target,
  NoDup subformulas -> List.In formula subformulas ->
  add_displacement (formula_remove subformulas formula) [source] = Some target ->
  Coq.Sorting.Permutation.Permutation
    (expand_counter_context subformulas source)
    (formula :: expand_counter_context subformulas target).
Proof.
  intros subformulas formula source target Hnodup Hin Happly.
  pose proof (formula_remove_displacement _ _ _ _ Happly) as Hsource.
  pose proof (expand_encode_counter_context_permutation subformulas
    (formula :: expand_counter_context subformulas target) Hnodup) as Hperm.
  assert (Hforall : List.Forall (fun item => List.In item subformulas)
      (formula :: expand_counter_context subformulas target)).
  { constructor; [exact Hin|apply expand_counter_context_forall]. }
  specialize (Hperm Hforall).
  rewrite encode_counter_context_cons,
    encode_expand_counter_context in Hperm by exact Hnodup.
  now rewrite <- Hsource in Hperm.
Qed.

Lemma formula_replace_displacement : forall subformulas old new source target,
  add_displacement (formula_replace subformulas old new) [source] = Some target ->
  nvec_add (encode_counter_context subformulas [new]) source =
  nvec_add (encode_counter_context subformulas [old]) target.
Proof.
  intros subformulas old new source target Happly.
  pose proof (add_displacement_exact_reduction _ _ _ _ Happly) as Hexact.
  rewrite nvec_sum_singleton_reduction in Hexact.
  unfold formula_replace in Hexact.
  rewrite formula_remove_encode_singleton,
    formula_add_encode_singleton in Hexact.
  apply (proj1 (Vector.eq_nth_iff nat _ _ _)).
  intros index index' Heq; subst index'.
  apply (f_equal (fun value => Vector.nth value index)) in Hexact.
  unfold nvec_to_zvec, zvec_add, nvec_add in Hexact |- *.
  repeat rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl)
    in Hexact.
  rewrite (nth_map Z.opp _ index index eq_refl) in Hexact.
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl) in Hexact.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma formula_replace_context_permutation : forall subformulas old new source target,
  NoDup subformulas -> List.In old subformulas -> List.In new subformulas ->
  add_displacement (formula_replace subformulas old new) [source] = Some target ->
  Coq.Sorting.Permutation.Permutation
    (new :: expand_counter_context subformulas source)
    (old :: expand_counter_context subformulas target).
Proof.
  intros subformulas old new source target Hnodup Hold Hnew Happly.
  pose proof (formula_replace_displacement _ _ _ _ _ Happly) as Heq.
  pose proof (expand_encode_counter_context_permutation subformulas
    (new :: expand_counter_context subformulas source) Hnodup) as Hleft.
  pose proof (expand_encode_counter_context_permutation subformulas
    (old :: expand_counter_context subformulas target) Hnodup) as Hright.
  assert (Hleft_all : List.Forall (fun item => List.In item subformulas)
      (new :: expand_counter_context subformulas source)).
  { constructor; [exact Hnew|apply expand_counter_context_forall]. }
  assert (Hright_all : List.Forall (fun item => List.In item subformulas)
      (old :: expand_counter_context subformulas target)).
  { constructor; [exact Hold|apply expand_counter_context_forall]. }
  specialize (Hleft Hleft_all); specialize (Hright Hright_all).
  rewrite encode_counter_context_cons,
    (encode_expand_counter_context subformulas source Hnodup) in Hleft.
  rewrite encode_counter_context_cons,
    (encode_expand_counter_context subformulas target Hnodup) in Hright.
  eapply Coq.Sorting.Permutation.Permutation_trans.
  - symmetry; exact Hleft.
  - rewrite Heq. exact Hright.
Qed.

Lemma formula_replace_context_decomposition : forall subformulas old new source target,
  NoDup subformulas -> List.In old subformulas -> List.In new subformulas ->
  old <> new ->
  add_displacement (formula_replace subformulas old new) [source] = Some target ->
  exists rest,
    Permutation (expand_counter_context subformulas source) (old :: rest) /\
    Permutation (expand_counter_context subformulas target) (new :: rest).
Proof.
  intros subformulas old new source target Hnodup Hold Hnew Hneq Happly.
  pose proof (formula_replace_context_permutation _ _ _ _ _
    Hnodup Hold Hnew Happly) as Hperm.
  assert (Hin : List.In old (expand_counter_context subformulas source)).
  { assert (Hin' : List.In old
        (new :: expand_counter_context subformulas source)).
    { eapply (Permutation_in old (Permutation_sym Hperm)). cbn; now left. }
    cbn in Hin'. destruct Hin' as [Heq | Hin].
    - exfalso. apply Hneq. now symmetry.
    - exact Hin. }
  apply List.in_split in Hin as [before [after Hsource]].
  exists (before ++ after). split.
  - rewrite Hsource. symmetry. apply Permutation_middle.
  - assert (Hmove : Permutation
        (old :: new :: before ++ after)
        (new :: expand_counter_context subformulas source)).
    { rewrite Hsource. cbn.
      change (Permutation (old :: (new :: before) ++ after)
        ((new :: before) ++ old :: after)).
      apply Permutation_middle. }
    pose proof (Permutation_trans Hmove Hperm) as Hfull.
    pose proof (Permutation_cons_inv Hfull) as Hresult.
    now symmetry.
Qed.

Lemma formula_replace_two_displacement : forall subformulas old first second
    source target,
  add_displacement
    (zvec_add (formula_remove subformulas old)
      (zvec_add (formula_add subformulas first)
        (formula_add subformulas second))) [source] = Some target ->
  nvec_add (encode_counter_context subformulas [old]) target =
  nvec_add (encode_counter_context subformulas [first])
    (nvec_add (encode_counter_context subformulas [second]) source).
Proof.
  intros subformulas old first second source target Happly.
  pose proof (add_displacement_exact_reduction _ _ _ _ Happly) as Hexact.
  rewrite nvec_sum_singleton_reduction in Hexact.
  rewrite !formula_remove_encode_singleton, !formula_add_encode_singleton in Hexact.
  apply (proj1 (Vector.eq_nth_iff nat _ _ _)).
  intros index index' Heq; subst index'.
  apply (f_equal (fun value => Vector.nth value index)) in Hexact.
  unfold zvec_add, nvec_add, nvec_to_zvec in Hexact |- *.
  repeat rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl)
    in Hexact.
  rewrite (nth_map Z.opp _ index index eq_refl) in Hexact.
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl) in Hexact.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma formula_replace_two_context_permutation : forall subformulas old first second
    source target,
  NoDup subformulas -> List.In old subformulas ->
  List.In first subformulas -> List.In second subformulas ->
  add_displacement
    (zvec_add (formula_remove subformulas old)
      (zvec_add (formula_add subformulas first)
        (formula_add subformulas second))) [source] = Some target ->
  Permutation (old :: expand_counter_context subformulas target)
    (first :: second :: expand_counter_context subformulas source).
Proof.
  intros subformulas old first second source target Hnodup Hold Hfirst Hsecond
    Happly.
  pose proof (formula_replace_two_displacement _ _ _ _ _ _ Happly) as Heq.
  pose proof (expand_encode_counter_context_permutation subformulas
    (old :: expand_counter_context subformulas target) Hnodup) as Hleft.
  pose proof (expand_encode_counter_context_permutation subformulas
    (first :: second :: expand_counter_context subformulas source) Hnodup)
    as Hright.
  specialize (Hleft ltac:(repeat constructor;
    auto using expand_counter_context_forall)).
  specialize (Hright ltac:(repeat constructor;
    auto using expand_counter_context_forall)).
  rewrite (encode_counter_context_cons subformulas old
      (expand_counter_context subformulas target)),
    (encode_expand_counter_context subformulas target Hnodup) in Hleft.
  rewrite (encode_counter_context_cons subformulas first
      (second :: expand_counter_context subformulas source)),
    (encode_counter_context_cons subformulas second
      (expand_counter_context subformulas source)),
    (encode_expand_counter_context subformulas source Hnodup) in Hright.
  eapply Permutation_trans; [symmetry; exact Hleft|].
  rewrite Heq. exact Hright.
Qed.

Lemma formula_replace_two_context_decomposition : forall subformulas old first second
    source target,
  NoDup subformulas -> List.In old subformulas ->
  List.In first subformulas -> List.In second subformulas ->
  old <> first -> old <> second ->
  add_displacement
    (zvec_add (formula_remove subformulas old)
      (zvec_add (formula_add subformulas first)
        (formula_add subformulas second))) [source] = Some target ->
  exists rest,
    Permutation (expand_counter_context subformulas source) (old :: rest) /\
    Permutation (expand_counter_context subformulas target)
      (first :: second :: rest).
Proof.
  intros subformulas old first second source target Hnodup Hold Hfirst Hsecond
    Hneq1 Hneq2 Happly.
  pose proof (formula_replace_two_context_permutation _ _ _ _ _ _ Hnodup
    Hold Hfirst Hsecond Happly) as Hperm.
  assert (Hin : List.In old (expand_counter_context subformulas source)).
  { assert (Hin' : List.In old
        (first :: second :: expand_counter_context subformulas source)).
    { eapply (Permutation_in old Hperm). cbn; now left. }
    cbn in Hin'. destruct Hin' as [Heq | [Heq | Hin]].
    - exfalso. apply Hneq1. now symmetry.
    - exfalso. apply Hneq2. now symmetry.
    - exact Hin. }
  apply List.in_split in Hin as [before [after Hsource]].
  exists (before ++ after). split.
  - rewrite Hsource. symmetry. apply Permutation_middle.
  - assert (Hmove : Permutation
        (first :: second :: expand_counter_context subformulas source)
        (old :: first :: second :: before ++ after)).
    { rewrite Hsource. cbn. symmetry.
      change (Permutation (old :: (first :: second :: before) ++ after)
        ((first :: second :: before) ++ old :: after)).
      apply Permutation_middle. }
    pose proof (Permutation_trans Hperm Hmove) as Hfull.
    exact (Permutation_cons_inv Hfull).
Qed.

Fixpoint store_context_support (support context : list IF.iformula) :
    list IF.iformula :=
  match context with
  | [] => support
  | IF.ioc A :: tail => store_context_support (add_support A support) tail
  | _ :: tail => store_context_support support tail
  end.

Fixpoint linear_context (context : list IF.iformula) : list IF.iformula :=
  match context with
  | [] => []
  | IF.ioc _ :: tail => linear_context tail
  | A :: tail => A :: linear_context tail
  end.

Definition support_difference (source target : list IF.iformula) :=
  List.filter
    (fun A => if in_dec iformula_eq_dec A source then false else true)
    target.

Lemma support_difference_in : forall source target A,
  List.In A (support_difference source target) <->
  List.In A target /\ ~ List.In A source.
Proof.
  intros source target A. unfold support_difference.
  rewrite List.filter_In. destruct (in_dec iformula_eq_dec A source)
    as [Hin | Hnot]; cbn.
  - split; [intros [_ Hfalse]; discriminate|tauto].
  - tauto.
Qed.

Lemma support_target_permutation : forall source target,
  NoDup source -> NoDup target -> List.incl source target ->
  Permutation target (source ++ support_difference source target).
Proof.
  intros source target Hsource Htarget Hincl.
  apply NoDup_Permutation.
  - exact Htarget.
  - apply NoDup_app; [exact Hsource|apply NoDup_filter; exact Htarget|].
    intros A HAsource HAdifference.
    apply support_difference_in in HAdifference. tauto.
  - intro A. rewrite List.in_app_iff, support_difference_in.
    split.
    + intro HAtarget. destruct (in_dec iformula_eq_dec A source).
      * now left.
      * right; tauto.
    + intros [HAsource | [HAtarget _]]; [apply Hincl|]; assumption.
Qed.

Lemma ill_support_weaken : forall source target linear conclusion,
  NoDup source -> NoDup target -> List.incl source target ->
  Yalla.ill_cut.ill_ll (support_context source ++ linear) conclusion ->
  Yalla.ill_cut.ill_ll (support_context target ++ linear) conclusion.
Proof.
  intros source target linear conclusion Hsource Htarget Hincl pi.
  pose proof (Yalla.ill_def.wk_list_ilr
    (support_difference source target) (support_context source) linear
    conclusion pi) as weakened.
  assert (Hperm : Permutation
      (support_context source ++
        List.map IF.ioc (support_difference source target) ++ linear)
      (support_context target ++ linear)).
  { unfold support_context. rewrite List.app_assoc.
    apply Permutation_app_tail.
    rewrite <- List.map_app. apply Permutation_map.
    symmetry. now apply support_target_permutation. }
  eapply ill_ll_permutation; [exact weakened|].
  exact Hperm.
Qed.

Lemma add_support_in : forall A support B,
  List.In B (add_support A support) <-> B = A \/ List.In B support.
Proof.
  intros A support B. unfold add_support.
  destruct (in_dec Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec
    A support); cbn; split; intro H.
  - right; exact H.
  - destruct H as [-> | H]; assumption.
  - destruct H as [H | H]; [left; symmetry|right]; exact H.
  - destruct H as [H | H]; [left; symmetry|right]; exact H.
Qed.

Lemma support_union_in : forall left right A,
  List.In A (support_union left right) <->
  List.In A left \/ List.In A right.
Proof.
  induction left as [|head tail IH]; intros right A.
  - unfold support_union; cbn. tauto.
  - change (List.In A (add_support head (support_union tail right)) <->
      List.In A (head :: tail) \/ List.In A right).
    rewrite add_support_in, IH. cbn. intuition congruence.
Qed.

Lemma support_union_nodup : forall left right,
  NoDup right -> NoDup (support_union left right).
Proof.
  induction left as [|head tail IH]; intros right Hright.
  - exact Hright.
  - change (NoDup (add_support head (support_union tail right))).
    unfold add_support. destruct
      (in_dec Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec head
        (support_union tail right)).
    + apply IH; exact Hright.
    + constructor; [exact n|apply IH; exact Hright].
Qed.

Lemma support_union_left_incl : forall left right,
  List.incl left (support_union left right).
Proof.
  intros left right A HA. apply support_union_in. now left.
Qed.

Lemma support_union_right_incl : forall left right,
  List.incl right (support_union left right).
Proof.
  intros left right A HA. apply support_union_in. now right.
Qed.

Lemma guarded_body_in : forall formulas A,
  List.In A
    (List.flat_map (fun formula =>
       match formula with IF.ioc body => [body] | _ => [] end) formulas) <->
  List.In (IF.ioc A) formulas.
Proof.
  intros formulas A. split.
  - intro H. apply List.in_flat_map in H as [formula [Hformula HA]].
    destruct formula; cbn in HA; try contradiction.
    destruct HA as [Heq | []]. subst. exact Hformula.
  - intro H. apply List.in_flat_map.
    exists (IF.ioc A). split; [exact H|cbn; now left].
Qed.

Lemma guarded_bodies_nodup : forall formulas,
  NoDup formulas ->
  NoDup (List.flat_map (fun formula =>
    match formula with IF.ioc body => [body] | _ => [] end) formulas).
Proof.
  induction formulas as [|formula tail IH]; intro Hnodup.
  - constructor.
  - inversion Hnodup as [|? ? Hnotin Htail]; subst.
    destruct formula; cbn in *; try (apply IH; exact Htail).
    constructor.
    + intro Hin. apply guarded_body_in in Hin. contradiction.
    + now apply IH.
Qed.

Lemma ilz_guarded_bodies_nodup : forall goal,
  NoDup (ilz_guarded_bodies goal).
Proof.
  intro goal. unfold ilz_guarded_bodies.
  apply guarded_bodies_nodup, ilz_subformulas_nodup.
Qed.

Lemma list_powerset_member_incl : forall (A : Type) (values subset : list A),
  List.In subset (list_powerset values) -> List.incl subset values.
Proof.
  intros A values; induction values as [|value tail IH];
    intros subset Hsubset.
  - cbn in Hsubset. destruct Hsubset as [<- | []]. intros x [] .
  - cbn in Hsubset. apply List.in_app_iff in Hsubset as [Hsubset | Hsubset].
    + intros x Hx. right. eapply IH; eauto.
    + apply List.in_map_iff in Hsubset as [rest [<- Hrest]].
      intros x [<- | Hx]; [now left|right; eapply IH; eauto].
Qed.

Lemma list_powerset_member_nodup : forall (A : Type) (values subset : list A),
  NoDup values -> List.In subset (list_powerset values) -> NoDup subset.
Proof.
  intros A values; induction values as [|value tail IH];
    intros subset Hvalues Hsubset.
  - cbn in Hsubset. destruct Hsubset as [<- | []]. constructor.
  - inversion Hvalues as [|? ? Hnotin Htail]; subst.
    cbn in Hsubset. apply List.in_app_iff in Hsubset as [Hsubset | Hsubset].
    + now apply IH with (subset := subset).
    + apply List.in_map_iff in Hsubset as [rest [<- Hrest]].
      constructor.
      * intro Hin. apply Hnotin.
        eapply list_powerset_member_incl; eauto.
      * now apply IH with (subset := rest).
Qed.

Lemma list_insertions_sound : forall (A : Type) (value : A) values result,
  List.In result (list_insertions value values) ->
  Permutation (value :: values) result.
Proof.
  intros A value values; induction values as [|head tail IH];
    intros result Hresult; cbn in Hresult.
  - destruct Hresult as [<- | []]. reflexivity.
  - destruct Hresult as [<- | Hresult].
    + reflexivity.
    + apply List.in_map_iff in Hresult as [rest [<- Hrest]].
      eapply Permutation_trans.
      * apply perm_swap.
      * constructor. now apply IH.
Qed.

Lemma list_insertions_complete : forall (A : Type) (value : A) before after,
  List.In (before ++ value :: after)
    (list_insertions value (before ++ after)).
Proof.
  intros A value before; induction before as [|head tail IH]; intros after; cbn.
  - destruct after; cbn; auto.
  - right. apply List.in_map_iff.
    exists (tail ++ value :: after). split; [reflexivity|apply IH].
Qed.

Lemma list_permutations_sound : forall (A : Type) (values result : list A),
  List.In result (list_permutations values) -> Permutation values result.
Proof.
  intros A values; induction values as [|head tail IH]; intros result Hresult.
  - cbn in Hresult. destruct Hresult as [<- | []]. reflexivity.
  - cbn in Hresult. apply List.in_flat_map in Hresult as [prior [Hprior Hresult]].
    eapply Permutation_trans.
    + apply perm_skip. exact (IH prior Hprior).
    + now apply list_insertions_sound.
Qed.

Lemma list_permutations_complete : forall (A : Type) (values result : list A),
  Permutation values result -> List.In result (list_permutations values).
Proof.
  intros A values; induction values as [|head tail IH]; intros result Hperm.
  - apply Permutation_nil in Hperm. subst result. cbn. now left.
  - assert (Hin : List.In head result).
    { apply (Permutation_in head Hperm). now left. }
    apply List.in_split in Hin as [before [after ->]].
    apply Permutation_cons_app_inv in Hperm.
    cbn. apply List.in_flat_map.
    exists (before ++ after). split.
    + now apply IH.
    + apply list_insertions_complete.
Qed.

Definition select_from {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (universe selected : list A) : list A :=
  List.filter (fun x => if in_dec eq_dec x selected then true else false)
    universe.

Lemma select_from_in_powerset : forall (A : Type)
    (eq_dec : forall x y : A, {x = y} + {x <> y}) universe selected,
  List.In (select_from eq_dec universe selected) (list_powerset universe).
Proof.
  intros A eq_dec universe. unfold select_from.
  induction universe as [|head tail IH]; intro selected; cbn.
  - now left.
  - destruct (in_dec eq_dec head selected).
    + apply List.in_app_iff. right. apply List.in_map_iff.
      exists (select_from eq_dec tail selected). split; [reflexivity|apply IH].
    + apply List.in_app_iff. left. apply IH.
Qed.

Lemma select_from_in : forall (A : Type)
    (eq_dec : forall x y : A, {x = y} + {x <> y}) universe selected x,
  List.In x (select_from eq_dec universe selected) <->
  List.In x universe /\ List.In x selected.
Proof.
  intros A eq_dec universe selected x. unfold select_from.
  rewrite List.filter_In. destruct (in_dec eq_dec x selected); cbn;
    intuition congruence.
Qed.

Lemma ilz_supports_complete : forall goal support,
  NoDup support -> List.incl support (ilz_guarded_bodies goal) ->
  List.In support (ilz_supports goal).
Proof.
  intros goal support Hnodup Hincl. unfold ilz_supports.
  set (canonical := select_from iformula_eq_dec
    (ilz_guarded_bodies goal) support).
  apply List.in_flat_map. exists canonical. split.
  - unfold canonical. apply select_from_in_powerset.
  - apply list_permutations_complete, NoDup_Permutation.
    + unfold canonical, select_from. apply NoDup_filter,
        ilz_guarded_bodies_nodup.
    + exact Hnodup.
    + intro A. unfold canonical. rewrite select_from_in.
      split.
      * intros [_ HA]. exact HA.
      * intro HA. split; [apply Hincl|]; exact HA.
Qed.

Lemma add_support_nodup : forall A support,
  NoDup support -> NoDup (add_support A support).
Proof.
  intros A support Hnodup. unfold add_support.
  destruct (in_dec Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec
    A support); [exact Hnodup|].
  now constructor.
Qed.

Lemma add_support_incl : forall universe A support,
  List.In A universe -> List.incl support universe ->
  List.incl (add_support A support) universe.
Proof.
  intros universe A support HA Hincl B HB.
  apply add_support_in in HB as [-> | HB]; [exact HA|now apply Hincl].
Qed.

Lemma support_union_incl : forall universe left right,
  List.incl left universe -> List.incl right universe ->
  List.incl (support_union left right) universe.
Proof.
  intros universe left right Hleft Hright A HA.
  apply support_union_in in HA as [HA | HA]; [now apply Hleft|now apply Hright].
Qed.

Lemma store_context_support_nodup : forall support context,
  NoDup support -> NoDup (store_context_support support context).
Proof.
  intros support context; revert support.
  induction context as [|formula tail IH]; intros support Hsupport; cbn.
  - exact Hsupport.
  - destruct formula; try now apply IH.
    apply IH, add_support_nodup, Hsupport.
Qed.

Lemma store_context_support_incl : forall goal support context,
  List.incl support (ilz_guarded_bodies goal) ->
  List.Forall (fun A => List.In A (ilz_subformulas goal)) context ->
  List.incl (store_context_support support context)
    (ilz_guarded_bodies goal).
Proof.
  intros goal support context; revert support.
  induction context as [|formula tail IH]; intros support Hsupport Hall; cbn.
  - exact Hsupport.
  - inversion Hall as [|? ? Hformula Htail]; subst.
    destruct formula as
        [atom | | A B | A B | A | A B | A | | A B | | A B | A];
      try now apply IH.
    apply IH; [|exact Htail]. apply add_support_incl.
    + apply (proj2 (guarded_body_in (ilz_subformulas goal) A)). exact Hformula.
    + exact Hsupport.
Qed.

Lemma ilz_support_nodup : forall goal support,
  List.In support (ilz_supports goal) -> NoDup support.
Proof.
  intros goal support Hsupport. unfold ilz_supports in Hsupport.
  apply List.in_flat_map in Hsupport as [subset [Hsubset Hsupport]].
  apply (Permutation_NoDup (list_permutations_sound _ _ _ Hsupport)).
  eapply list_powerset_member_nodup; [apply ilz_guarded_bodies_nodup|].
  exact Hsubset.
Qed.

Lemma ilz_support_incl : forall goal support,
  List.In support (ilz_supports goal) ->
  List.incl support (ilz_guarded_bodies goal).
Proof.
  intros goal support Hsupport. unfold ilz_supports in Hsupport.
  apply List.in_flat_map in Hsupport as [subset [Hsubset Hperm]].
  pose proof (list_permutations_sound _ _ _ Hperm) as Hpermutation.
  intros A HA. apply (Permutation_in A (Permutation_sym Hpermutation)) in HA.
  eapply list_powerset_member_incl; eauto.
Qed.

Lemma store_context_support_in : forall goal support context,
  List.In support (ilz_supports goal) ->
  List.Forall (fun A => List.In A (ilz_subformulas goal)) context ->
  List.In (store_context_support support context) (ilz_supports goal).
Proof.
  intros goal support context Hsupport Hall. apply ilz_supports_complete.
  - apply store_context_support_nodup, ilz_support_nodup with (goal := goal).
    exact Hsupport.
  - apply store_context_support_incl; [now apply ilz_support_incl|exact Hall].
Qed.

Lemma ilz_guarded_body_subformula : forall goal A,
  List.In A (ilz_guarded_bodies goal) ->
  List.In A (ilz_subformulas goal).
Proof.
  intros goal A HA. apply guarded_body_in in HA.
  apply ilz_subformulas_sound in HA as [root [Hroot Hsub]].
  eapply ilz_subformulas_complete; [exact Hroot|].
  eapply IF.isub_trans; [apply IF.isub_oc; constructor|exact Hsub].
Qed.

Lemma ilz_subformula_child : forall goal parent child,
  List.In parent (ilz_subformulas goal) -> IF.isubform child parent ->
  List.In child (ilz_subformulas goal).
Proof.
  intros goal parent child Hparent Hchild.
  apply ilz_subformulas_sound in Hparent as [root [Hroot Hsub]].
  eapply ilz_subformulas_complete; [exact Hroot|].
  exact (IF.isub_trans child parent root Hchild Hsub).
Qed.

Lemma ill_linear_permutation : forall support left right conclusion,
  Permutation left right ->
  inhabited (Yalla.ill_cut.ill_ll (support_context support ++ left) conclusion) ->
  inhabited (Yalla.ill_cut.ill_ll (support_context support ++ right) conclusion).
Proof.
  intros support left right conclusion Hperm [pi]. constructor.
  eapply ill_ll_permutation; [exact pi|].
  now apply Permutation_app_head.
Qed.

Lemma ill_support_merge_tens : forall left_support right_support
    left_linear right_linear A B,
  NoDup left_support -> NoDup right_support ->
  inhabited (Yalla.ill_cut.ill_ll
    (support_context left_support ++ left_linear) A) ->
  inhabited (Yalla.ill_cut.ill_ll
    (support_context right_support ++ right_linear) B) ->
  inhabited (Yalla.ill_cut.ill_ll
    (support_context (support_union left_support right_support) ++
      left_linear ++ right_linear) (IF.itens A B)).
Proof.
  intros left_support right_support left_linear right_linear A B
    Hleft_nodup Hright_nodup Hleft Hright.
  destruct Hleft as [Hleft]. destruct Hright as [Hright].
  set (union := support_union left_support right_support).
  assert (Hunion : NoDup union).
  { unfold union. now apply support_union_nodup. }
  pose proof (ill_support_weaken left_support union left_linear A
    Hleft_nodup Hunion (support_union_left_incl _ _) Hleft)
    as left_proof.
  pose proof (ill_support_weaken right_support union right_linear B
    Hright_nodup Hunion (support_union_right_incl _ _) Hright)
    as right_proof.
  assert (tensor_proof : Yalla.ill_cut.ill_ll
      ((support_context union ++ left_linear) ++
       support_context union ++ right_linear) (IF.itens A B)).
  { apply Yalla.ill_def.tens_irr; assumption. }
  assert (duplicated : Yalla.ill_cut.ill_ll
      (support_context union ++ support_context union ++
       left_linear ++ right_linear) (IF.itens A B)).
  { eapply ill_ll_permutation; [exact tensor_proof|].
    repeat rewrite <- List.app_assoc.
    apply Permutation_app_head.
    apply Permutation_app_swap_app. }
  constructor. unfold support_context in *.
  exact (Yalla.ill_def.co_list_ilr union [] (left_linear ++ right_linear)
    (IF.itens A B) duplicated).
Qed.

Lemma ill_support_merge_lmap : forall left_support right_support
    left_linear right_linear A B C,
  NoDup left_support -> NoDup right_support ->
  inhabited (Yalla.ill_cut.ill_ll
    (support_context left_support ++ left_linear) A) ->
  inhabited (Yalla.ill_cut.ill_ll
    (support_context right_support ++ B :: right_linear) C) ->
  inhabited (Yalla.ill_cut.ill_ll
    (support_context (support_union left_support right_support) ++
      IF.ilmap A B :: left_linear ++ right_linear) C).
Proof.
  intros left_support right_support left_linear right_linear A B C
    Hleft_nodup Hright_nodup Hleft Hright.
  destruct Hleft as [Hleft]. destruct Hright as [Hright].
  set (union := support_union left_support right_support).
  assert (Hunion : NoDup union).
  { unfold union. now apply support_union_nodup. }
  pose proof (ill_support_weaken left_support union left_linear A
    Hleft_nodup Hunion (support_union_left_incl _ _) Hleft)
    as left_proof.
  pose proof (ill_support_weaken right_support union (B :: right_linear) C
    Hright_nodup Hunion (support_union_right_incl _ _) Hright)
    as right_proof.
  assert (raw : Yalla.ill_cut.ill_ll
      (support_context union ++
       (support_context union ++ left_linear) ++
       IF.ilmap A B :: right_linear) C).
  { eapply Yalla.ill_def.lmap_ilr; eassumption. }
  assert (duplicated : Yalla.ill_cut.ill_ll
      (support_context union ++ support_context union ++
       left_linear ++ IF.ilmap A B :: right_linear) C).
  { eapply ill_ll_permutation; [exact raw|].
    repeat rewrite List.app_assoc. reflexivity. }
  assert (contracted : Yalla.ill_cut.ill_ll
      (support_context union ++ left_linear ++ IF.ilmap A B :: right_linear) C).
  { unfold support_context in *.
    exact (Yalla.ill_def.co_list_ilr union []
      (left_linear ++ IF.ilmap A B :: right_linear) C duplicated). }
  constructor. eapply ill_ll_permutation; [exact contracted|].
  apply Permutation_app_head. symmetry. apply Permutation_middle.
Qed.

Lemma ill_linear_derelict_into_support : forall support A linear conclusion,
  List.In A support ->
  inhabited (Yalla.ill_cut.ill_ll
    (support_context support ++ A :: linear) conclusion) ->
  inhabited (Yalla.ill_cut.ill_ll
    (support_context support ++ linear) conclusion).
Proof.
  intros support A linear conclusion Hin [pi].
  apply List.in_split in Hin as [before [after ->]].
  unfold support_context in *.
  rewrite List.map_app in *; cbn in *.
  assert (derelicted : Yalla.ill_cut.ill_ll
      ((List.map IF.ioc before ++ IF.ioc A :: List.map IF.ioc after) ++
        IF.ioc A :: linear) conclusion).
  { apply Yalla.ill_def.de_ilr. exact pi. }
  assert (duplicated : Yalla.ill_cut.ill_ll
      (List.map IF.ioc before ++ IF.ioc A :: IF.ioc A ::
        List.map IF.ioc after ++ linear) conclusion).
  { eapply ill_ll_permutation; [exact derelicted|].
    repeat rewrite <- List.app_assoc.
    apply Permutation_app_head.
    cbn. constructor. symmetry. apply Permutation_middle. }
  constructor. rewrite <- List.app_assoc.
  apply Yalla.ill_def.co_ilr. exact duplicated.
Qed.

Definition mk_unary {d} source delta target : UnaryZeroRule d ILZMachineState :=
  {| unary_zero_source := source;
     unary_zero_delta := delta;
     unary_zero_target := target |}.

Definition mk_split source left right : SplitZeroRule ILZMachineState :=
  {| split_zero_source := source;
     split_zero_left := left;
     split_zero_right := right |}.

Definition mk_zero source target : FullZeroRule ILZMachineState :=
  {| full_zero_source := source; full_zero_target := target |}.

Definition ilz_sequent_states (goal : ILZGoal) : list ILZMachineState :=
  List.flat_map (fun support =>
    List.map (ilz_machine_sequent support) (ilz_subformulas goal))
    (ilz_supports goal).

Definition ilz_store_rules (goal : ILZGoal) :=
  let subformulas := ilz_subformulas goal in
  List.flat_map (fun state =>
    match state with
    | ilz_machine_sequent support conclusion =>
        List.flat_map (fun guarded =>
          match guarded with
          | IF.ioc A =>
              [mk_unary (ilz_machine_sequent support conclusion)
                 (formula_remove subformulas guarded)
                 (ilz_machine_sequent (add_support A support) conclusion);
               mk_unary (ilz_machine_sequent (add_support A support) conclusion)
                 (formula_add subformulas A)
                 (ilz_machine_sequent (add_support A support) conclusion)]
          | _ => []
          end) (ilz_guarded_subformulas goal)
    | _ => []
    end) (ilz_sequent_states goal).

Definition ilz_logical_unary_rules (goal : ILZGoal) :=
  let subformulas := ilz_subformulas goal in
  List.flat_map (fun state =>
    match state with
    | ilz_machine_sequent support conclusion =>
        List.flat_map (fun formula =>
          match formula with
          | IF.ione =>
              [mk_unary (ilz_machine_sequent support conclusion)
                 (formula_remove subformulas IF.ione)
                 (ilz_machine_sequent support conclusion)]
          | IF.itens A B =>
              [mk_unary (ilz_machine_sequent support conclusion)
                 (zvec_add (formula_remove subformulas formula)
                   (zvec_add (formula_add subformulas A)
                     (formula_add subformulas B)))
                 (ilz_machine_sequent support conclusion)]
          | IF.ilmap A B =>
              [mk_unary (ilz_machine_sequent support formula)
                 (formula_add subformulas A)
                 (ilz_machine_sequent support B)]
          | IF.ineg A =>
              [mk_unary (ilz_machine_sequent support formula)
                 (formula_add subformulas A)
                 (ilz_machine_sequent support IF.N);
               mk_unary (ilz_machine_sequent support IF.N)
                 (formula_remove subformulas formula)
                 (ilz_machine_sequent support A)]
          | IF.ioc A =>
              [mk_unary (ilz_machine_sequent support conclusion)
                 (formula_replace subformulas formula A)
                 (ilz_machine_sequent support conclusion);
               mk_unary (ilz_machine_sequent support conclusion)
                 (formula_remove subformulas formula)
                 (ilz_machine_sequent support conclusion);
               mk_unary (ilz_machine_sequent support conclusion)
                 (formula_remove subformulas formula)
                 (ilz_machine_contract support conclusion A);
               mk_unary (ilz_machine_contract support conclusion A)
                 (zvec_add (formula_add subformulas formula)
                   (formula_add subformulas formula))
                 (ilz_machine_sequent support conclusion)]
          | _ => []
          end) subformulas
    | _ => []
    end) (ilz_sequent_states goal).

Definition ilz_lmap_split_unary_rules (goal : ILZGoal) :=
  let subformulas := ilz_subformulas goal in
  let supports := ilz_supports goal in
  List.flat_map (fun left_support =>
    List.flat_map (fun right_support =>
      List.flat_map (fun formula =>
        match formula with
        | IF.ilmap A B =>
            List.flat_map (fun conclusion =>
              let left_state := ilz_machine_sequent left_support A in
              let right_pending :=
                ilz_machine_lmap_right right_support conclusion B in
              [mk_unary
                 (ilz_machine_sequent
                   (List.fold_right add_support right_support left_support)
                   conclusion)
                 (formula_remove subformulas formula)
                 (ilz_machine_split left_state right_pending);
               mk_unary right_pending (formula_add subformulas B)
                 (ilz_machine_sequent right_support conclusion)]) subformulas
        | _ => []
        end) subformulas) supports) supports.

Definition ilz_split_rules (goal : ILZGoal) :=
  let subformulas := ilz_subformulas goal in
  let supports := ilz_supports goal in
  List.flat_map (fun left_support =>
    List.flat_map (fun right_support =>
      List.flat_map (fun formula =>
        match formula with
        | IF.itens A B =>
            [mk_split
              (ilz_machine_sequent
                (List.fold_right add_support right_support left_support) formula)
              (ilz_machine_sequent left_support A)
              (ilz_machine_sequent right_support B)]
        | _ => []
        end) subformulas) supports) supports ++
  List.flat_map (fun left_support =>
    List.flat_map (fun right_support =>
      List.flat_map (fun A =>
        List.flat_map (fun B =>
          List.map (fun conclusion =>
            let left_state := ilz_machine_sequent left_support A in
            let right_pending :=
              ilz_machine_lmap_right right_support conclusion B in
            mk_split (ilz_machine_split left_state right_pending)
              left_state right_pending) subformulas) subformulas) subformulas)
      supports) supports.

Definition ilz_initial_rules (goal : ILZGoal) :=
  let subformulas := ilz_subformulas goal in
  List.flat_map (fun support =>
    List.flat_map (fun formula =>
      match formula with
      | IF.ivar _ =>
          [mk_unary (ilz_machine_sequent support formula)
             (formula_remove subformulas formula) ilz_machine_leaf]
      | IF.ione =>
          [mk_unary (ilz_machine_sequent support IF.ione)
             (zvec_zero (length subformulas)) ilz_machine_leaf]
      | IF.ioc A =>
          if in_dec Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec
              A support then
            [mk_unary (ilz_machine_sequent support formula)
               (zvec_zero (length subformulas)) ilz_machine_leaf]
          else []
      | _ => []
      end) subformulas) (ilz_supports goal).

Definition ilz_zero_rules (goal : ILZGoal) :=
  List.flat_map (fun support =>
    List.flat_map (fun formula =>
      match formula with
      | IF.ioc A =>
          [mk_zero (ilz_machine_sequent support formula)
             (ilz_machine_sequent support A)]
      | _ => []
      end) (ilz_subformulas goal)) (ilz_supports goal).

Definition compile_ilz_machine (goal : ILZGoal) :
    FullZeroBVASS (length (ilz_subformulas goal)) ILZMachineState :=
  {| full_zero_leaves := [ilz_machine_leaf];
     full_zero_unary_rules :=
       ilz_initial_rules goal ++ ilz_store_rules goal ++
       ilz_logical_unary_rules goal ++ ilz_lmap_split_unary_rules goal;
     full_zero_split_rules := ilz_split_rules goal;
     full_zero_test_rules := ilz_zero_rules goal |}.

Lemma compile_ilz_machine_runtime_eq : forall goal,
  Mell.Reduction.MELLToABVASSRuntime.compile_ilz_machine goal =
  compile_ilz_machine goal.
Proof. reflexivity. Qed.

Definition ilz_machine_accepts (goal : ILZGoal) : Prop :=
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent [] (snd goal))
    (nvec_zero (length (ilz_subformulas goal))).

Lemma ilz_sequent_state_in : forall goal support conclusion,
  List.In support (ilz_supports goal) ->
  List.In conclusion (ilz_subformulas goal) ->
  List.In (ilz_machine_sequent support conclusion) (ilz_sequent_states goal).
Proof.
  intros goal support conclusion Hsupport Hconclusion.
  unfold ilz_sequent_states. apply List.in_flat_map.
  exists support. split; [exact Hsupport|].
  apply List.in_map_iff. exists conclusion. auto.
Qed.

Lemma ilz_guarded_subformula_in : forall goal A,
  List.In (IF.ioc A) (ilz_subformulas goal) ->
  List.In (IF.ioc A) (ilz_guarded_subformulas goal).
Proof.
  intros goal A HA. unfold ilz_guarded_subformulas.
  apply List.filter_In. split; [exact HA|reflexivity].
Qed.

Lemma ilz_store_move_rule_in : forall goal support conclusion A,
  List.In support (ilz_supports goal) ->
  List.In conclusion (ilz_subformulas goal) ->
  List.In (IF.ioc A) (ilz_subformulas goal) ->
  List.In
    (mk_unary (ilz_machine_sequent support conclusion)
      (formula_remove (ilz_subformulas goal) (IF.ioc A))
      (ilz_machine_sequent (add_support A support) conclusion))
    (full_zero_unary_rules (compile_ilz_machine goal)).
Proof.
  intros goal support conclusion A Hsupport Hconclusion HA. cbn.
  apply List.in_or_app. right. apply List.in_or_app. left.
  unfold ilz_store_rules. apply List.in_flat_map.
  exists (ilz_machine_sequent support conclusion). split.
  - now apply ilz_sequent_state_in.
  - apply List.in_flat_map. exists (IF.ioc A). split.
    + now apply ilz_guarded_subformula_in.
    + cbn. now left.
Qed.

Fixpoint ILZMachineStateValid (goal : ILZGoal) (state : ILZMachineState)
    (counters : NVec (length (ilz_subformulas goal))) : Prop :=
  match state with
  | ilz_machine_leaf => counters = nvec_zero (length (ilz_subformulas goal))
  | ilz_machine_sequent support conclusion =>
      inhabited (Yalla.ill_cut.ill_ll
        (machine_context (ilz_subformulas goal) support counters) conclusion)
  | ilz_machine_split left_state right_state =>
      exists left_counters right_counters,
        counters = nvec_add left_counters right_counters /\
        ILZMachineStateValid goal left_state left_counters /\
        ILZMachineStateValid goal right_state right_counters
  | ilz_machine_contract support conclusion A =>
      inhabited (Yalla.ill_cut.ill_ll
        (support_context support ++ IF.ioc A :: IF.ioc A ::
          expand_counter_context (ilz_subformulas goal) counters) conclusion)
  | ilz_machine_lmap_right support conclusion B =>
      inhabited (Yalla.ill_cut.ill_ll
        (support_context support ++ B ::
          expand_counter_context (ilz_subformulas goal) counters) conclusion)
  end.

Definition UnaryRuleSound (goal : ILZGoal)
    (rule : UnaryZeroRule (length (ilz_subformulas goal)) ILZMachineState) : Prop :=
  forall source_counters target_counters,
    add_displacement (unary_zero_delta _ _ rule) [source_counters] =
      Some target_counters ->
    ILZMachineStateValid goal (unary_zero_target _ _ rule) target_counters ->
    ILZMachineStateValid goal (unary_zero_source _ _ rule) source_counters.

Definition SplitRuleSound (goal : ILZGoal)
    (rule : SplitZeroRule ILZMachineState) : Prop :=
  forall source_counters left_counters right_counters,
    source_counters = nvec_add left_counters right_counters ->
    ILZMachineStateValid goal (split_zero_left _ rule) left_counters ->
    ILZMachineStateValid goal (split_zero_right _ rule) right_counters ->
    ILZMachineStateValid goal (split_zero_source _ rule) source_counters.

Definition ZeroRuleSound (goal : ILZGoal)
    (rule : FullZeroRule ILZMachineState) : Prop :=
  ILZMachineStateValid goal (full_zero_target _ rule)
    (nvec_zero (length (ilz_subformulas goal))) ->
  ILZMachineStateValid goal (full_zero_source _ rule)
    (nvec_zero (length (ilz_subformulas goal))).

Theorem ilz_initial_rules_sound : forall goal,
  List.Forall (UnaryRuleSound goal) (ilz_initial_rules goal).
Proof.
  intro goal. apply List.Forall_forall.
  intros rule Hrule. unfold ilz_initial_rules in Hrule.
  apply in_flat_map in Hrule as [support [Hsupport Hrule]].
  apply in_flat_map in Hrule as [formula [Hformula Hrule]].
  destruct formula as
      [atom | | A B | A B | A | A B | A | | A B | | A B | A];
    cbn in Hrule; try contradiction.
  - destruct Hrule as [<- | []]. unfold UnaryRuleSound; cbn.
    intros source target Happly Htarget.
    pose proof (formula_remove_context_permutation
      (ilz_subformulas goal) (IF.ivar atom) source target
      (ilz_subformulas_nodup goal) Hformula Happly) as Hperm.
    subst target. constructor.
    unfold machine_context.
    eapply ill_support_weaken;
      [constructor|exact (ilz_support_nodup goal support Hsupport)|intros ? []|].
    eapply ill_ll_permutation.
    + apply Yalla.ill_def.ax_ir.
    + symmetry. rewrite expand_counter_context_zero in Hperm. exact Hperm.
  - destruct Hrule as [<- | []]. unfold UnaryRuleSound; cbn.
    intros source target Happly Htarget.
    pose proof (zero_displacement_reduction _ _ _ Happly) as ->.
    subst source. unfold machine_context.
    rewrite expand_counter_context_zero. constructor.
    eapply ill_support_weaken;
      [constructor|exact (ilz_support_nodup goal support Hsupport)|intros ? []|].
    apply Yalla.ill_def.one_irr.
  - destruct (in_dec Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec
      A support) as [Hin | Hnotin];
      cbn in Hrule; try contradiction.
    destruct Hrule as [<- | []]. unfold UnaryRuleSound; cbn.
    intros source target Happly Htarget.
    pose proof (zero_displacement_reduction _ _ _ Happly) as ->.
    subst source. unfold machine_context.
    rewrite expand_counter_context_zero. constructor.
    eapply ill_support_weaken with (source := [A]) (target := support)
      (linear := []) (conclusion := IF.ioc A).
    + repeat constructor. intro H; inversion H.
    + exact (ilz_support_nodup goal support Hsupport).
    + intros item [<- | []]. exact Hin.
    + cbn. apply Yalla.ill_def.ax_exp_ill.
Qed.

Theorem ilz_store_rules_sound : forall goal,
  List.Forall (UnaryRuleSound goal) (ilz_store_rules goal).
Proof.
  intro goal. apply List.Forall_forall.
  intros rule Hrule. unfold ilz_store_rules in Hrule.
  apply List.in_flat_map in Hrule as [state [Hstate Hrule]].
  destruct state as
      [support conclusion | left right | support conclusion A |
       support conclusion B |];
    try contradiction.
  apply List.in_flat_map in Hrule as [guarded [Hguarded Hrule]].
  destruct guarded as
      [atom | | A B | A B | A | A B | A | | A B | | A B | A];
    cbn in Hrule; try contradiction.
  apply List.filter_In in Hguarded as [Hguarded _].
  destruct Hrule as [<- | [<- | []]]; unfold UnaryRuleSound; cbn;
    intros source target Happly Htarget.
  - pose proof (formula_remove_context_permutation
      (ilz_subformulas goal) (IF.ioc A) source target
      (ilz_subformulas_nodup goal) Hguarded Happly) as Hperm.
    assert (moved : inhabited (Yalla.ill_cut.ill_ll
        (support_context support ++ IF.ioc A ::
          expand_counter_context (ilz_subformulas goal) target)
        conclusion)).
    { unfold add_support in Htarget.
      destruct (in_dec Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec
        A support) as [Hin | Hnotin].
      - destruct Htarget as [pi]. constructor.
        exact (Yalla.ill_def.wk_list_ilr [A] (support_context support)
          (expand_counter_context (ilz_subformulas goal) target)
          conclusion pi).
      - destruct Htarget as [pi]. constructor.
        unfold support_context in *. cbn in pi.
        eapply ill_ll_permutation; [exact pi|].
        apply Permutation_middle. }
    destruct moved as [pi]. constructor.
    eapply ill_ll_permutation; [exact pi|].
    apply Permutation_app_head. symmetry. exact Hperm.
  - pose proof (formula_add_context_permutation
      (ilz_subformulas goal) A source target
      (ilz_subformulas_nodup goal)
      (ilz_guarded_body_subformula goal A
        (proj2 (guarded_body_in (ilz_subformulas goal) A) Hguarded))
      Happly) as Hperm.
    assert (expanded : inhabited (Yalla.ill_cut.ill_ll
        (support_context (add_support A support) ++ A ::
          expand_counter_context (ilz_subformulas goal) source)
        conclusion)).
    { destruct Htarget as [pi]. constructor.
      eapply ill_ll_permutation; [exact pi|].
      apply Permutation_app_head. exact Hperm. }
    eapply ill_linear_derelict_into_support; [|exact expanded].
    apply add_support_in. now left.
Qed.

Theorem ilz_logical_unary_rules_sound : forall goal,
  List.Forall (UnaryRuleSound goal) (ilz_logical_unary_rules goal).
Proof.
  intro goal. apply List.Forall_forall.
  intros rule Hrule. unfold ilz_logical_unary_rules in Hrule.
  apply List.in_flat_map in Hrule as [state [Hstate Hrule]].
  destruct state as
      [support conclusion | left right | support conclusion body |
       support conclusion B |];
    try contradiction.
  apply List.in_flat_map in Hrule as [formula [Hformula Hrule]].
  destruct formula as
      [atom | | A B | A B | A | A B | A | | A B | | A B | A];
    cbn in Hrule; try contradiction.
  - destruct Hrule as [<- | []]. unfold UnaryRuleSound; cbn.
    intros source target Happly Htarget.
    pose proof (formula_remove_context_permutation
      (ilz_subformulas goal) IF.ione source target
      (ilz_subformulas_nodup goal) Hformula Happly) as Hperm.
    destruct Htarget as [pi]. constructor.
    assert (with_one : Yalla.ill_cut.ill_ll
        (support_context support ++ IF.ione ::
          expand_counter_context (ilz_subformulas goal) target) conclusion).
    { apply Yalla.ill_def.one_ilr. exact pi. }
    eapply ill_ll_permutation; [exact with_one|].
    apply Permutation_app_head. symmetry. exact Hperm.
  - destruct Hrule as [<- | []]. unfold UnaryRuleSound; cbn.
    intros source target Happly Htarget.
    assert (HA : List.In A (ilz_subformulas goal)).
    { eapply ilz_subformula_child; [exact Hformula|apply IF.isub_tens_l; constructor]. }
    assert (HB : List.In B (ilz_subformulas goal)).
    { eapply ilz_subformula_child; [exact Hformula|apply IF.isub_tens_r; constructor]. }
    destruct (formula_replace_two_context_decomposition
      (ilz_subformulas goal) (IF.itens A B) A B source target
      (ilz_subformulas_nodup goal) Hformula HA HB
      ltac:(intro Heq; apply (f_equal IF.ifsize) in Heq; cbn in Heq; lia)
      ltac:(intro Heq; apply (f_equal IF.ifsize) in Heq; cbn in Heq; lia)
      Happly)
      as [rest [Hsource Htargetperm]].
    destruct (ill_linear_permutation support _ _ conclusion Htargetperm Htarget)
      as [pi].
    constructor.
    assert (folded : Yalla.ill_cut.ill_ll
        (support_context support ++ IF.itens A B :: rest) conclusion).
    { apply Yalla.ill_def.tens_ilr. exact pi. }
    eapply ill_ll_permutation; [exact folded|].
    apply Permutation_app_head. symmetry. exact Hsource.
  - destruct Hrule as [<- | []]. unfold UnaryRuleSound; cbn.
    intros source target Happly Htarget.
    pose proof (formula_add_context_permutation
      (ilz_subformulas goal) A source target
      (ilz_subformulas_nodup goal)
      (ilz_subformula_child goal (IF.ilmap A B) A Hformula
        (IF.isub_lmap_l A A B (IF.isub_id A))) Happly) as Hperm.
    destruct (ill_linear_permutation support _ _ B Hperm Htarget) as [pi].
    assert (front : Yalla.ill_cut.ill_ll
        (A :: support_context support ++
          expand_counter_context (ilz_subformulas goal) source) B).
    { eapply ill_ll_permutation; [exact pi|].
      symmetry. apply Permutation_middle. }
    constructor. now apply Yalla.ill_def.lmap_irr.
  - destruct Hrule as [<- | [<- | []]].
    + unfold UnaryRuleSound; cbn. intros source target Happly Htarget.
      pose proof (formula_add_context_permutation
        (ilz_subformulas goal) A source target
        (ilz_subformulas_nodup goal)
        (ilz_subformula_child goal (IF.ineg A) A Hformula
          (IF.isub_neg A A (IF.isub_id A))) Happly) as Hperm.
      destruct (ill_linear_permutation support _ _ IF.N Hperm Htarget) as [pi].
      assert (front : Yalla.ill_cut.ill_ll
          (A :: support_context support ++
            expand_counter_context (ilz_subformulas goal) source) IF.N).
      { eapply ill_ll_permutation; [exact pi|].
        symmetry. apply Permutation_middle. }
      constructor. now apply Yalla.ill_def.neg_irr.
    + unfold UnaryRuleSound; cbn. intros source target Happly Htarget.
      pose proof (formula_remove_context_permutation
        (ilz_subformulas goal) (IF.ineg A) source target
        (ilz_subformulas_nodup goal) Hformula Happly) as Hperm.
      destruct Htarget as [pi].
      assert (with_neg : Yalla.ill_cut.ill_ll
          (support_context support ++ IF.ineg A ::
            expand_counter_context (ilz_subformulas goal) target) IF.N).
      { assert (tail_neg : Yalla.ill_cut.ill_ll
            ((support_context support ++
              expand_counter_context (ilz_subformulas goal) target) ++
              [IF.ineg A]) IF.N).
        { apply Yalla.ill_def.neg_ilr. exact pi. }
        eapply ill_ll_permutation; [exact tail_neg|].
        repeat rewrite <- List.app_assoc.
        apply Permutation_app_head.
        replace (IF.ineg A ::
            expand_counter_context (ilz_subformulas goal) target)
          with (IF.ineg A ::
            expand_counter_context (ilz_subformulas goal) target ++ [])
          by now rewrite List.app_nil_r.
        exact (Permutation_sym
          (@Permutation_middle IF.iformula
            (expand_counter_context (ilz_subformulas goal) target) []
            (IF.ineg A))). }
      constructor. eapply ill_ll_permutation; [exact with_neg|].
      apply Permutation_app_head. symmetry. exact Hperm.
  - destruct Hrule as [<- | [<- | [<- | [<- | []]]]].
    + unfold UnaryRuleSound; cbn. intros source target Happly Htarget.
      assert (HA : List.In A (ilz_subformulas goal)).
      { eapply ilz_subformula_child; [exact Hformula|apply IF.isub_oc; constructor]. }
      destruct (formula_replace_context_decomposition
        (ilz_subformulas goal) (IF.ioc A) A source target
        (ilz_subformulas_nodup goal) Hformula HA
        ltac:(intro Heq; apply (f_equal IF.ifsize) in Heq; cbn in Heq; lia)
        Happly)
        as [rest [Hsource Htargetperm]].
      destruct (ill_linear_permutation support _ _ conclusion Htargetperm Htarget)
        as [pi].
      constructor.
      assert (derelicted : Yalla.ill_cut.ill_ll
          (support_context support ++ IF.ioc A :: rest) conclusion).
      { apply Yalla.ill_def.de_ilr. exact pi. }
      eapply ill_ll_permutation; [exact derelicted|].
      apply Permutation_app_head. symmetry. exact Hsource.
    + unfold UnaryRuleSound; cbn. intros source target Happly Htarget.
      pose proof (formula_remove_context_permutation
        (ilz_subformulas goal) (IF.ioc A) source target
        (ilz_subformulas_nodup goal) Hformula Happly) as Hperm.
      destruct Htarget as [pi]. constructor.
      assert (weakened : Yalla.ill_cut.ill_ll
          (support_context support ++ IF.ioc A ::
            expand_counter_context (ilz_subformulas goal) target) conclusion).
      { apply Yalla.ill_def.wk_ilr. exact pi. }
      eapply ill_ll_permutation; [exact weakened|].
      apply Permutation_app_head. symmetry. exact Hperm.
    + unfold UnaryRuleSound; cbn. intros source target Happly Htarget.
      pose proof (formula_remove_context_permutation
        (ilz_subformulas goal) (IF.ioc A) source target
        (ilz_subformulas_nodup goal) Hformula Happly) as Hperm.
      destruct Htarget as [pi]. constructor.
      assert (contracted : Yalla.ill_cut.ill_ll
          (support_context support ++ IF.ioc A ::
            expand_counter_context (ilz_subformulas goal) target) conclusion).
      { apply Yalla.ill_def.co_ilr. exact pi. }
      eapply ill_ll_permutation; [exact contracted|].
      apply Permutation_app_head. symmetry. exact Hperm.
    + unfold UnaryRuleSound; cbn. intros source target Happly Htarget.
      pose proof (formula_add_two_context_permutation
        (ilz_subformulas goal) (IF.ioc A) source target
        (ilz_subformulas_nodup goal) Hformula Happly) as Hperm.
      destruct Htarget as [pi]. constructor.
      eapply ill_ll_permutation; [exact pi|].
      apply Permutation_app_head. exact Hperm.
Qed.

Theorem ilz_lmap_split_unary_rules_sound : forall goal,
  List.Forall (UnaryRuleSound goal) (ilz_lmap_split_unary_rules goal).
Proof.
  intro goal. apply List.Forall_forall.
  intros rule Hrule. unfold ilz_lmap_split_unary_rules in Hrule.
  apply List.in_flat_map in Hrule as [left_support [Hleft_support Hrule]].
  apply List.in_flat_map in Hrule as [right_support [Hright_support Hrule]].
  apply List.in_flat_map in Hrule as [formula [Hformula Hrule]].
  destruct formula as
      [atom | | A B | A B | A | A B | A | | A B | | A B | A];
    cbn in Hrule; try contradiction.
  apply List.in_flat_map in Hrule as [conclusion [Hconclusion Hrule]].
  destruct Hrule as [<- | [<- | []]].
  - unfold UnaryRuleSound; cbn. intros source target Happly Htarget.
    destruct Htarget as [left_counters [right_counters
      [Htarget [Hleft Hright]]]].
    subst target.
    pose proof (formula_remove_context_permutation
      (ilz_subformulas goal) (IF.ilmap A B) source
      (nvec_add left_counters right_counters)
      (ilz_subformulas_nodup goal) Hformula Happly) as Hremove.
    pose proof (expand_counter_context_add (ilz_subformulas goal)
      left_counters right_counters (ilz_subformulas_nodup goal)) as Hadd.
    pose proof (ill_support_merge_lmap left_support right_support
      (expand_counter_context (ilz_subformulas goal) left_counters)
      (expand_counter_context (ilz_subformulas goal) right_counters)
      A B conclusion
      (ilz_support_nodup goal left_support Hleft_support)
      (ilz_support_nodup goal right_support Hright_support)
      Hleft Hright) as merged.
    destruct merged as [pi]. constructor.
    eapply ill_ll_permutation; [exact pi|].
    apply Permutation_app_head.
    eapply Permutation_trans.
    + apply perm_skip. symmetry. exact Hadd.
    + symmetry. exact Hremove.
  - unfold UnaryRuleSound; cbn. intros source target Happly Htarget.
    pose proof (formula_add_context_permutation
      (ilz_subformulas goal) B source target
      (ilz_subformulas_nodup goal)
      (ilz_subformula_child goal (IF.ilmap A B) B Hformula
        (IF.isub_lmap_r B B A (IF.isub_id B))) Happly) as Hperm.
    destruct Htarget as [pi]. constructor.
    eapply ill_ll_permutation; [exact pi|].
    apply Permutation_app_head. exact Hperm.
Qed.

Theorem ilz_split_rules_sound : forall goal,
  List.Forall (SplitRuleSound goal) (ilz_split_rules goal).
Proof.
  intro goal. apply List.Forall_forall.
  intros rule Hrule. unfold ilz_split_rules in Hrule.
  apply List.in_app_iff in Hrule as [Hrule | Hrule].
  - apply List.in_flat_map in Hrule as [left_support [Hleft_support Hrule]].
    apply List.in_flat_map in Hrule as [right_support [Hright_support Hrule]].
    apply List.in_flat_map in Hrule as [formula [Hformula Hrule]].
    destruct formula as
        [atom | | A B | A B | A | A B | A | | A B | | A B | A];
      cbn in Hrule; try contradiction.
    destruct Hrule as [<- | []]. unfold SplitRuleSound; cbn.
    intros source left_counters right_counters Hsource Hleft Hright.
    subst source.
    pose proof (ill_support_merge_tens left_support right_support
      (expand_counter_context (ilz_subformulas goal) left_counters)
      (expand_counter_context (ilz_subformulas goal) right_counters)
      A B
      (ilz_support_nodup goal left_support Hleft_support)
      (ilz_support_nodup goal right_support Hright_support)
      Hleft Hright) as merged.
    pose proof (expand_counter_context_add (ilz_subformulas goal)
      left_counters right_counters (ilz_subformulas_nodup goal)) as Hadd.
    eapply ill_linear_permutation; [symmetry; exact Hadd|exact merged].
  - apply List.in_flat_map in Hrule as [left_support [_ Hrule]].
    apply List.in_flat_map in Hrule as [right_support [_ Hrule]].
    apply List.in_flat_map in Hrule as [A [_ Hrule]].
    apply List.in_flat_map in Hrule as [B [_ Hrule]].
    apply List.in_map_iff in Hrule as [conclusion [<- _]].
    unfold SplitRuleSound; cbn.
    intros source left_counters right_counters Hsource Hleft Hright.
    exists left_counters, right_counters. auto.
Qed.

Theorem ilz_zero_rules_sound : forall goal,
  List.Forall (ZeroRuleSound goal) (ilz_zero_rules goal).
Proof.
  intro goal. apply List.Forall_forall.
  intros rule Hrule. unfold ilz_zero_rules in Hrule.
  apply List.in_flat_map in Hrule as [support [_ Hrule]].
  apply List.in_flat_map in Hrule as [formula [_ Hrule]].
  destruct formula as
      [atom | | A B | A B | A | A B | A | | A B | | A B | A];
    cbn in Hrule; try contradiction.
  destruct Hrule as [<- | []]. unfold ZeroRuleSound; cbn.
  intro Htarget. unfold machine_context, support_context in *.
  rewrite expand_counter_context_zero in Htarget |- *.
  rewrite !List.app_nil_r in Htarget |- *.
  destruct Htarget as [pi]. constructor.
  now apply Yalla.ill_def.oc_irr.
Qed.

Theorem full_zero_reach_sound_from_rules : forall goal state counters,
  List.Forall (UnaryRuleSound goal)
    (full_zero_unary_rules (compile_ilz_machine goal)) ->
  List.Forall (SplitRuleSound goal)
    (full_zero_split_rules (compile_ilz_machine goal)) ->
  List.Forall (ZeroRuleSound goal)
    (full_zero_test_rules (compile_ilz_machine goal)) ->
  FullZeroReach (compile_ilz_machine goal) state counters ->
  ILZMachineStateValid goal state counters.
Proof.
  intros goal state counters Hunary Hsplit Hzero Hreach.
  induction Hreach.
  - cbn in *. destruct H as [<- | []]. reflexivity.
  - eapply (proj1 (List.Forall_forall _ _) Hunary rule H); eauto.
  - eapply (proj1 (List.Forall_forall _ _) Hsplit rule H); eauto.
  - eapply (proj1 (List.Forall_forall _ _) Hzero rule H); eauto.
Qed.

Theorem ilz_machine_rules_sound : forall goal,
  List.Forall (UnaryRuleSound goal)
    (full_zero_unary_rules (compile_ilz_machine goal)) /\
  List.Forall (SplitRuleSound goal)
    (full_zero_split_rules (compile_ilz_machine goal)) /\
  List.Forall (ZeroRuleSound goal)
    (full_zero_test_rules (compile_ilz_machine goal)).
Proof.
  intro goal. split.
  - change (List.Forall (UnaryRuleSound goal)
      (ilz_initial_rules goal ++ ilz_store_rules goal ++
       ilz_logical_unary_rules goal ++ ilz_lmap_split_unary_rules goal)).
    apply List.Forall_app. split.
    + apply ilz_initial_rules_sound.
    + apply List.Forall_app. split.
      * apply ilz_store_rules_sound.
      * apply List.Forall_app. split.
        -- apply ilz_logical_unary_rules_sound.
        -- apply ilz_lmap_split_unary_rules_sound.
  - split.
    + change (List.Forall (SplitRuleSound goal) (ilz_split_rules goal)).
      apply ilz_split_rules_sound.
    + change (List.Forall (ZeroRuleSound goal) (ilz_zero_rules goal)).
      apply ilz_zero_rules_sound.
Qed.

Theorem ilz_machine_sound : forall goal,
  fst goal = [] -> ilz_machine_accepts goal -> ILZProvable goal.
Proof.
  intros goal Hleft Hreach.
  destruct (ilz_machine_rules_sound goal) as [Hunary [Hsplit Hzero]].
  pose proof (full_zero_reach_sound_from_rules goal _ _
    Hunary Hsplit Hzero Hreach) as Hvalid.
  unfold ilz_machine_accepts, ILZMachineStateValid in Hvalid.
  unfold machine_context, support_context in Hvalid; cbn in Hvalid.
  rewrite expand_counter_context_zero in Hvalid. cbn in Hvalid.
  unfold ILZProvable. now rewrite Hleft.
Qed.

Theorem ilz_machine_fork_free : forall goal,
  ForkFreeFullZeroBVASS (compile_ilz_machine goal).
Proof. intros; exact I. Qed.
