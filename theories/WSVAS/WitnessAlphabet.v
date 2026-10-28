From Coq Require Import List Vector VectorSpec ZArith Lia.
From KruskalTrees Require Import idx vec.
From KruskalAfProp Require Import af.af af.af_tools.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Runs Contexts RunOrder Amalgamation.
From Mell.Order Require Import FiniteBasis AlmostFullBridge.
From Mell.Semilinear Require Import Presentation LinearEquations.
From Mell.VAS Require Import Runs JancarOrder.
From Mell.Separator Require Import TransformerPeriod.
From Mell.WSVAS Require Import System Runs.

Import ListNotations idx_notations.

Section WitnessAlphabet.
Context {d : nat} (S : IBVAS d) (code : SemiCode d).

Definition component_at (index : idx (length code)) : LinearComponent d :=
  vas_nth_idx code index.

Definition ComponentCoefficients (index : idx (length code)) :=
  NVec (length (snd (component_at index))).

Definition component_contribution (index : idx (length code))
    (coefficients : ComponentCoefficients index) : NVec d :=
  match weighted_sum (Vector.to_list coefficients) (snd (component_at index)) with
  | Some value => value
  | None => nvec_zero d
  end.

Definition component_value (index : idx (length code))
    (coefficients : ComponentCoefficients index) : NVec d :=
  nvec_add (fst (component_at index))
    (component_contribution index coefficients).

Definition RunWitness := { run : IRun d | ValidIRun S run }.
Definition ComponentWitness := sigT ComponentCoefficients.
Definition WitnessAlphabet := (RunWitness + ComponentWitness)%type.

Definition witness_value (witness : WitnessAlphabet) : NVec d :=
  match witness with
  | inl run => irun_target (proj1_sig run)
  | inr (existT index coefficients) => component_value index coefficients
  end.

Definition component_witness_le (left right : ComponentWitness) : Prop :=
  match left, right with
  | existT left_index left_coefficients,
    existT right_index right_coefficients =>
      exists equality : left_index = right_index,
        nvec_le (eq_rect left_index ComponentCoefficients left_coefficients
          right_index equality) right_coefficients
  end.

Definition witness_le (left right : WitnessAlphabet) : Prop :=
  match left, right with
  | inl left_run, inl right_run => IRunLe (proj1_sig left_run) (proj1_sig right_run)
  | inr left_component, inr right_component =>
      component_witness_le left_component right_component
  | _, _ => False
  end.

Lemma witness_le_refl : forall witness, witness_le witness witness.
Proof.
  intros [[run Hrun]|[index coefficients]]; cbn.
  - apply irun_le_refl.
  - exists eq_refl. apply nvec_le_refl.
Qed.

Lemma witness_le_trans : forall x y z,
  witness_le x y -> witness_le y z -> witness_le x z.
Proof.
  intros [[xr Hxr]|[xi xv]] [[yr Hyr]|[yi yv]] [[zr Hzr]|[zi zv]] Hxy Hyz;
    cbn in *; try contradiction.
  - eapply irun_le_trans; eauto.
  - destruct Hxy as [E1 H1], Hyz as [E2 H2]. destruct E1, E2.
    exists eq_refl. eapply nvec_le_trans; eauto.
Qed.

Lemma weighted_sum_vector_total : forall (periods : list (NVec d))
    (coefficients : NVec (length periods)),
  exists contribution,
    weighted_sum (Vector.to_list coefficients) periods = Some contribution.
Proof.
  induction periods as [|period periods IH]; intro coefficients.
  - refine (Vector.case0 (fun coefficients => exists contribution,
      weighted_sum (Vector.to_list coefficients) [] = Some contribution) _ coefficients).
    exists (nvec_zero d). reflexivity.
  - refine (Vector.caseS' coefficients (fun coefficients => exists contribution,
      weighted_sum (Vector.to_list coefficients) (period :: periods) = Some contribution) _).
    intros coefficient tail.
    destruct (IH tail) as [contribution Hcontribution].
    exists (nvec_add (nvec_scale coefficient period) contribution).
    change (match weighted_sum (Vector.to_list tail) periods with
      | Some value => Some (nvec_add (nvec_scale coefficient period) value)
      | None => None
      end = Some (nvec_add (nvec_scale coefficient period) contribution)).
    destruct (weighted_sum (Vector.to_list tail) periods) as [value|] eqn:Hsum.
    + assert (Some value = Some contribution) as Heq.
      { exact (eq_trans (eq_sym Hsum) Hcontribution). }
      inversion Heq; subst. reflexivity.
    + assert (@None (NVec d) = Some contribution) as Heq.
      { exact (eq_trans (eq_sym Hsum) Hcontribution). }
      discriminate.
Qed.

Lemma component_contribution_spec : forall index coefficients,
  weighted_sum (Vector.to_list coefficients) (snd (component_at index)) =
    Some (component_contribution index coefficients).
Proof.
  intros index coefficients. unfold component_contribution.
  destruct (weighted_sum_vector_total (snd (component_at index)) coefficients)
    as [value Hvalue]. rewrite Hvalue. reflexivity.
Qed.

Lemma component_value_denotes : forall index coefficients,
  linear_denote (component_at index) (component_value index coefficients).
Proof.
  intros index coefficients. unfold linear_denote, component_value.
  exists (Vector.to_list coefficients), (component_contribution index coefficients).
  split; [apply component_contribution_spec|reflexivity].
Qed.

Lemma weighted_sum_some_lengths : forall coefficients periods contribution,
  @weighted_sum d coefficients periods = Some contribution ->
  length coefficients = length periods.
Proof.
  induction coefficients as [|coefficient coefficients IH];
    destruct periods as [|period periods]; intros contribution Hsum;
    cbn in Hsum; try discriminate; auto.
  destruct (weighted_sum coefficients periods) eqn:Htail; try discriminate.
  cbn. f_equal. eapply IH; eauto.
Qed.

Lemma linear_denote_has_coefficients : forall component value,
  linear_denote component value ->
  exists coefficients : NVec (length (snd component)),
    value = nvec_add (fst component)
      (match weighted_sum (Vector.to_list coefficients) (snd component) with
       | Some contribution => contribution
       | None => nvec_zero d
       end).
Proof.
  intros [base periods] value [coefficients [contribution [Hsum Hvalue]]].
  cbn in *.
  pose proof (weighted_sum_some_lengths coefficients periods contribution Hsum)
    as Hlength.
  destruct Hlength.
  exists (Vector.of_list coefficients).
  rewrite to_list_of_list_opp, Hsum. exact Hvalue.
Qed.

Lemma component_at_in : forall index, List.In (component_at index) code.
Proof.
  intro index. unfold component_at, vas_nth_idx.
  rewrite <- (to_list_of_list_opp code).
  apply (proj1 (Vector.to_list_In _ _ _ _)). apply Vector.In_nth.
Qed.

Lemma witness_value_in_union : forall witness,
  Reach S (witness_value witness) \/ denote code (witness_value witness).
Proof.
  intros [[run Hvalid]|[index coefficients]].
  - left. now apply valid_irun_reach.
  - right. exists (component_at index). split.
    + apply component_at_in.
    + apply component_value_denotes.
Qed.

Lemma witness_value_complete : forall value,
  Reach S value \/ denote code value ->
  exists witness, witness_value witness = value.
Proof.
  intros value [Hreach|Hdenote].
  - destruct (reach_valid_irun_mut d S) as [Hruns _].
    destruct (Hruns value Hreach) as [run [Hvalid Htarget]].
    exists (inl (exist _ run Hvalid)). cbn. exact Htarget.
  - destruct Hdenote as [component [Hin Hlinear]].
    destruct (vas_nth_idx_occurrence _ code component Hin) as [index Hindex].
    destruct (linear_denote_has_coefficients component value Hlinear)
      as [coefficients Hvalue].
    subst component.
    exists (inr (@existT _ ComponentCoefficients index coefficients)).
    unfold witness_value, component_value, component_contribution. cbn.
    unfold component_at. symmetry. exact Hvalue.
Qed.

Fixpoint coefficient_list_add (left right : list nat) : list nat :=
  match left, right with
  | x :: xs, y :: ys => Nat.add x y :: coefficient_list_add xs ys
  | _, _ => []
  end.

Lemma nvec_add_cons_local : forall n left_head right_head
    (left_tail right_tail : NVec n),
  nvec_add (Vector.cons nat left_head n left_tail)
    (Vector.cons nat right_head n right_tail) =
  Vector.cons nat (Nat.add left_head right_head) n
    (nvec_add left_tail right_tail).
Proof.
  intros n left_head right_head left_tail right_tail.
  apply (proj1 (Vector.eq_nth_iff nat (Nat.succ n) _ _)). intros i j Hij; subst j.
  refine (Fin.caseS' i (fun i => Vector.nth
    (nvec_add (Vector.cons nat left_head n left_tail)
      (Vector.cons nat right_head n right_tail)) i =
    Vector.nth (Vector.cons nat (Nat.add left_head right_head) n
      (nvec_add left_tail right_tail)) i) _ _).
  - unfold nvec_add. rewrite (Vector.nth_map2 Nat.add _ _ Fin.F1 Fin.F1 Fin.F1
      eq_refl eq_refl). reflexivity.
  - intro tail_index. unfold nvec_add.
    rewrite (Vector.nth_map2 Nat.add _ _ (Fin.FS tail_index)
      (Fin.FS tail_index) (Fin.FS tail_index) eq_refl eq_refl).
    cbn. rewrite (Vector.nth_map2 Nat.add left_tail right_tail tail_index
      tail_index tail_index eq_refl eq_refl).
    reflexivity.
Qed.

Lemma vector_to_list_nvec_add : forall n (left right : NVec n),
  Vector.to_list (nvec_add left right) =
    coefficient_list_add (Vector.to_list left) (Vector.to_list right).
Proof.
  intros n left right.
  refine (Vector.rect2
    (fun n left right => Vector.to_list (nvec_add left right) =
      coefficient_list_add (Vector.to_list left) (Vector.to_list right))
    _ _ left right).
  - reflexivity.
  - intros m left_tail right_tail IH left_head right_head.
    rewrite nvec_add_cons_local. cbn. f_equal. exact IH.
Qed.

Lemma weighted_sum_coefficient_list_add : forall periods left right lv rv,
  @weighted_sum d left periods = Some lv ->
  weighted_sum right periods = Some rv ->
  weighted_sum (coefficient_list_add left right) periods =
    Some (nvec_add lv rv).
Proof.
  induction periods as [|period periods IH];
    destruct left as [|lh lt], right as [|rh rt];
    intros lv rv Hl Hr; cbn in *; try discriminate.
  - inversion Hl; inversion Hr; subst. rewrite nvec_add_zero_left_local.
    reflexivity.
  - destruct (weighted_sum lt periods) as [ltv|] eqn:Hlt; try discriminate.
    destruct (weighted_sum rt periods) as [rtv|] eqn:Hrt; try discriminate.
    inversion Hl; inversion Hr; subst.
    rewrite (IH lt rt ltv rtv Hlt Hrt), nvec_scale_add_coeff,
      nvec_add_shuffle. reflexivity.
Qed.

Lemma weighted_sum_vector_add : forall periods
    (left right : NVec (length periods)) left_value right_value,
  @weighted_sum d (Vector.to_list left) periods = Some left_value ->
  weighted_sum (Vector.to_list right) periods = Some right_value ->
  weighted_sum (Vector.to_list (nvec_add left right)) periods =
    Some (nvec_add left_value right_value).
Proof.
  intros. rewrite vector_to_list_nvec_add.
  now eapply weighted_sum_coefficient_list_add.
Qed.

Lemma component_contribution_add : forall index left right,
  component_contribution index (nvec_add left right) =
    nvec_add (component_contribution index left)
      (component_contribution index right).
Proof.
  intros index left right.
  pose proof (component_contribution_spec index left) as Hl.
  pose proof (component_contribution_spec index right) as Hr.
  pose proof (weighted_sum_vector_add (snd (component_at index)) left right
    _ _ Hl Hr) as Hadd.
  pose proof (component_contribution_spec index (nvec_add left right)) as Hsum.
  congruence.
Qed.

Lemma component_value_add_offsets : forall index root left_offset right_offset,
  nvec_add (component_value index root)
    (component_value index
      (nvec_add (nvec_add root left_offset) right_offset)) =
  nvec_add (component_value index (nvec_add root left_offset))
    (component_value index (nvec_add root right_offset)).
Proof.
  intros index root left_offset right_offset.
  unfold component_value.
  repeat rewrite component_contribution_add.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros i j Hij; subst j. unfold nvec_add.
  repeat rewrite (Vector.nth_map2 Nat.add _ _ i i i eq_refl eq_refl). lia.
Qed.

Lemma component_witness_le_wqo : af component_witness_le.
Proof.
  pose proof (@af_dep_sum (length code) ComponentCoefficients
    (fun index => @nvec_le (length (snd (component_at index))))) as Hdep.
  eapply af_mono; [|apply Hdep].
  - intros [li lv] [ri rv] H. exact H.
  - intro index. apply nvec_le_almost_full.
Qed.

Lemma run_witness_le_wqo :
  af (fun left right : RunWitness => IRunLe (proj1_sig left) (proj1_sig right)).
Proof.
  apply (proj1 (@afs_iff_af_sub_rel (IRun d) (ValidIRun S) IRunLe)).
  apply irun_le_wqo.
Qed.

Theorem witness_alphabet_wqo : af witness_le.
Proof.
  eapply af_mono; [|apply af_sum; [apply run_witness_le_wqo|apply component_witness_le_wqo]].
  intros [left|left] [right|right]; cbn; auto.
Qed.

Lemma witness_value_monotone : forall left right,
  witness_le left right -> nvec_le (witness_value left) (witness_value right).
Proof.
  intros [[lr Hlr]|[li lc]] [[rr Hrr]|[ri rc]] Hle; cbn in *; try contradiction.
  - exact (proj1 Hle).
  - destruct Hle as [Heq Hcoeff]. destruct Heq. cbn in *.
    destruct (nvec_le_offset_witness _ _ _ Hcoeff) as [offset Hoff].
    subst rc. unfold component_value. rewrite component_contribution_add.
    intro i. unfold nvec_add.
    repeat rewrite (Vector.nth_map2 Nat.add _ _ i i i eq_refl eq_refl). lia.
Qed.

Definition witness_action (witness : WitnessAlphabet) : ZVec d :=
  nvec_to_zvec (witness_value witness).

Lemma zvec_add_comm_witness : forall (left right : ZVec d),
  zvec_add left right = zvec_add right left.
Proof.
  intros left right. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros i j Hij; subst j. unfold zvec_add.
  repeat rewrite (Vector.nth_map2 Z.add _ _ i i i eq_refl eq_refl). lia.
Qed.

Lemma witness_action_monotone : forall left right,
  witness_le left right -> zvec_le (witness_action left) (witness_action right).
Proof.
  intros left right Hle i. pose proof (witness_value_monotone left right Hle i).
  unfold witness_action, nvec_to_zvec.
  repeat rewrite (Vector.nth_map Z.of_nat _ i i eq_refl). lia.
Qed.

Theorem witness_alphabet_diamond : forall root left right,
  witness_le root left -> witness_le root right ->
  exists merged,
    witness_le left merged /\ witness_le right merged /\
    zvec_add (witness_action root) (witness_action merged) =
      zvec_add (witness_action left) (witness_action right).
Proof.
  intros [[root_run Hroot]|[root_index root_coeff]]
    [[left_run Hleft]|[left_index left_coeff]]
    [[right_run Hright]|[right_index right_coeff]] Hrl Hrr;
    cbn in *; try contradiction.
  - destruct (run_amalgamation d S root_run left_run right_run
      Hroot Hleft Hright Hrl Hrr)
      as [merged [Hmerged [Hlm [Hrm Heq]]]].
    exists (inl (exist _ merged Hmerged)). split; [exact Hlm|].
    split; [exact Hrm|].
    unfold witness_action, witness_value; cbn.
    rewrite <- !nvec_to_zvec_add. now rewrite Heq.
  - destruct Hrl as [Hel Hcl], Hrr as [Her Hcr]. destruct Hel, Her. cbn in *.
    destruct (nvec_le_offset_witness _ _ _ Hcl) as [lo Hlo].
    destruct (nvec_le_offset_witness _ _ _ Hcr) as [ro Hro].
    subst left_coeff right_coeff.
    set (merged_coeff := nvec_add (nvec_add root_coeff lo) ro).
    exists (inr (@existT _ ComponentCoefficients root_index merged_coeff)).
    repeat split.
    + exists eq_refl. unfold merged_coeff. apply nvec_le_add_right.
    + exists eq_refl. unfold merged_coeff.
      rewrite nvec_add_assoc_local,
        (nvec_add_comm (length (snd (component_at root_index))) lo ro),
        <- nvec_add_assoc_local. apply nvec_le_add_right.
    + unfold witness_action, witness_value; cbn.
      rewrite <- !nvec_to_zvec_add.
      f_equal. unfold merged_coeff. apply component_value_add_offsets.
Qed.

Fixpoint witness_actions_sum {n} (witnesses : Vector.t WitnessAlphabet n) : ZVec d :=
  match witnesses with
  | @Vector.nil _ => zvec_zero d
  | @Vector.cons _ witness _ tail =>
      zvec_add (witness_action witness) (witness_actions_sum tail)
  end.

Lemma witness_actions_sum_values : forall n
    (witnesses : Vector.t WitnessAlphabet n),
  witness_actions_sum witnesses =
    nvec_to_zvec
      (nvec_rsum (Vector.to_list (Vector.map witness_value witnesses))).
Proof.
  intros n witnesses. induction witnesses as [|head n tail IH]; cbn.
  - apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros i j Hij; subst j.
    unfold zvec_zero, nvec_to_zvec, nvec_zero.
    rewrite (Vector.const_nth Z 0 d i),
      (Vector.nth_map Z.of_nat _ i i eq_refl),
      (Vector.const_nth nat O d i). reflexivity.
  - rewrite nvec_to_zvec_add, IH.
    reflexivity.
Qed.

Lemma witness_actions_sum_monotone : forall n
    (left right : Vector.t WitnessAlphabet n),
  vec_fall2 witness_le left right ->
  zvec_le (witness_actions_sum left) (witness_actions_sum right).
Proof.
  intros n left right H. induction H using vec_fall2_rect.
  - apply zvec_le_refl.
  - unfold zvec_le in IHvec_fall2 |- *. intro i.
    cbn [witness_actions_sum]. unfold zvec_add.
    repeat rewrite (Vector.nth_map2 Z.add _ _ i i i eq_refl eq_refl).
    pose proof (witness_action_monotone x y H i) as Hhead.
    pose proof (IHvec_fall2 i) as Htail. apply Z.add_le_mono; assumption.
Qed.

Lemma witness_actions_sum_diamond : forall n
    (root left right : Vector.t WitnessAlphabet n),
  vec_fall2 witness_le root left -> vec_fall2 witness_le root right ->
  exists merged,
    vec_fall2 witness_le left merged /\
    vec_fall2 witness_le right merged /\
    zvec_add (witness_actions_sum root) (witness_actions_sum merged) =
      zvec_add (witness_actions_sum left) (witness_actions_sum right).
Proof.
  intros n root left right Hleft Hright.
  refine ((Vector.rect2
    (fun n root left =>
      vec_fall2 witness_le root left ->
      forall right : Vector.t WitnessAlphabet n,
      vec_fall2 witness_le root right ->
      exists merged,
        vec_fall2 witness_le left merged /\
        vec_fall2 witness_le right merged /\
        zvec_add (witness_actions_sum root) (witness_actions_sum merged) =
          zvec_add (witness_actions_sum left) (witness_actions_sum right))
    _ _ root left) Hleft right Hright).
  - intros _ right0.
    refine (Vector.case0
      (fun right => vec_fall2 witness_le (Vector.nil WitnessAlphabet) right -> _)
      _ right0).
    intros _. exists (Vector.nil WitnessAlphabet). split; [apply vec_fall2_nil|].
    split; [apply vec_fall2_nil|].
    apply (proj1 (Vector.eq_nth_iff Z d _ _)).
    intros i j Hij; subst j. unfold zvec_add, zvec_zero.
    repeat rewrite (Vector.nth_map2 Z.add _ _ i i i eq_refl eq_refl).
    repeat rewrite (Vector.const_nth Z 0 d i). lia.
  - intros m root_tail left_tail IH root_head left_head Hleft_cons right0.
    apply vec_fall2_cons_inv in Hleft_cons as [Hhead_left Htail_left].
    refine (Vector.caseS'
      right0
      (fun right => vec_fall2 witness_le
        (Vector.cons WitnessAlphabet root_head m root_tail) right -> _)
      _).
    intros right_head right_tail Hright_cons.
    apply vec_fall2_cons_inv in Hright_cons as [Hhead_right Htail_right].
    destruct (witness_alphabet_diamond root_head left_head right_head
      Hhead_left Hhead_right) as [head [Hlm [Hrm Heq]]].
    destruct (IH Htail_left right_tail Htail_right)
      as [tail [Hlt [Hrt Htail]]].
    exists (Vector.cons WitnessAlphabet head m tail). split.
    + apply vec_fall2_cons; assumption.
    + split; [apply vec_fall2_cons; assumption|].
      cbn [witness_actions_sum].
      apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros i j Hij; subst j.
      pose proof (f_equal (fun value : ZVec d => Vector.nth value i) Heq) as Heqi.
      pose proof (f_equal (fun value : ZVec d => Vector.nth value i) Htail) as Hti.
      unfold zvec_add in *.
      repeat rewrite (Vector.nth_map2 Z.add _ _ i i i eq_refl eq_refl) in *.
      lia.
Qed.

Definition action_at (index : idx (length (system_actions S))) : Action d :=
  vas_nth_idx (system_actions S) index.

Definition SideWitnesses (index : idx (length (system_actions S))) :=
  Vector.t WitnessAlphabet (Nat.pred (action_arity (action_at index))).

Definition ConcreteTransition := sigT SideWitnesses.

Definition concrete_transition_le (left right : ConcreteTransition) : Prop :=
  match left, right with
  | existT left_index left_witnesses, existT right_index right_witnesses =>
      exists equality : left_index = right_index,
        vec_fall2 witness_le
          (eq_rect left_index SideWitnesses left_witnesses right_index equality)
          right_witnesses
  end.

Definition concrete_transition_action (transition : ConcreteTransition) : ZVec d :=
  match transition with
  | existT index witnesses =>
      zvec_add (action_offset (action_at index)) (witness_actions_sum witnesses)
  end.

Lemma concrete_transition_wqo : af concrete_transition_le.
Proof.
  pose proof (@af_dep_sum (length (system_actions S)) SideWitnesses
    (fun index => @vec_fall2 WitnessAlphabet WitnessAlphabet witness_le
      (Nat.pred (action_arity (action_at index))))) as Hdep.
  eapply af_mono; [|apply Hdep].
  - intros [li lv] [ri rv] H. exact H.
  - intro index. apply af_vec_fall2. apply witness_alphabet_wqo.
Qed.

Lemma concrete_transition_le_refl : forall transition,
  concrete_transition_le transition transition.
Proof.
  intros [index witnesses]. exists eq_refl.
  intro position. apply witness_le_refl.
Qed.

Lemma concrete_transition_le_trans : forall x y z,
  concrete_transition_le x y -> concrete_transition_le y z ->
  concrete_transition_le x z.
Proof.
  intros [xi xv] [yi yv] [zi zv] [Hxy Hx] [Hyz Hy].
  destruct Hxy, Hyz. exists eq_refl. cbn in *.
  intro position. eapply witness_le_trans; [apply Hx|apply Hy].
Qed.

Definition concrete_wsvas : WSVAS d.
Proof.
  refine {| ws_transition := ConcreteTransition;
    ws_transition_le := concrete_transition_le;
    ws_transition_le_refl := concrete_transition_le_refl;
    ws_transition_le_trans := concrete_transition_le_trans;
    ws_transition_wqo := concrete_transition_wqo;
    ws_transition_action := concrete_transition_action |}.
  - intros [li lv] [ri rv] [Heq Hle]. destruct Heq. cbn in *.
    intro i. unfold concrete_transition_action, zvec_add.
    repeat rewrite (Vector.nth_map2 Z.add _ _ i i i eq_refl eq_refl).
    pose proof (witness_actions_sum_monotone _ _ _ Hle i). lia.
  - intros [ri roots] [li lefts] [qi rights] [Hrl Hleft] [Hrr Hright].
    destruct Hrl, Hrr. cbn in *.
    destruct (witness_actions_sum_diamond _ roots lefts rights Hleft Hright)
      as [merged [Hlm [Hrm Heq]]].
    exists (@existT _ SideWitnesses ri merged). repeat split; auto; try now exists eq_refl.
    unfold concrete_transition_action; cbn.
    apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros i j Hij; subst j.
    pose proof (f_equal (fun value : ZVec d => Vector.nth value i) Heq) as Hei.
    unfold zvec_add in *.
    repeat rewrite (Vector.nth_map2 Z.add _ _ i i i eq_refl eq_refl) in *.
    lia.
Defined.

Definition BVASSideStep (source target : NVec d) : Prop :=
  exists (rule_index : idx (length (system_actions S)))
    (side_values : list (NVec d)),
    length side_values = Nat.pred (action_arity (action_at rule_index)) /\
    List.Forall (fun value => Reach S value \/ denote code value) side_values /\
    apply_action (action_at rule_index) (source :: side_values) = Some target.

Lemma concrete_transition_step_apply_iff : forall
    (rule_index : idx (length (system_actions S)))
    (side_witnesses : SideWitnesses rule_index) source target,
  concrete_transition_action
      (@existT _ SideWitnesses rule_index side_witnesses) =
      StepAction source target <->
  apply_action (action_at rule_index)
      (source :: Vector.to_list (Vector.map witness_value side_witnesses)) =
      Some target.
Proof.
  intros rule_index side_witnesses source target.
  unfold concrete_transition_action. cbn. rewrite witness_actions_sum_values.
  assert (Hlength :
      length (source :: Vector.to_list (Vector.map witness_value side_witnesses)) =
      action_arity (action_at rule_index)).
  { cbn. rewrite Vector.length_to_list. apply Nat.succ_pred_pos.
    exact (action_arity_positive (action_at rule_index)). }
  unfold apply_action. rewrite (proj2 (Nat.eqb_eq _ _) Hlength).
  unfold add_displacement.
  rewrite nvec_sum_rsum. cbn. rewrite nvec_to_zvec_add.
  split; intro Heq.
  - replace (zvec_add (action_offset (action_at rule_index))
        (zvec_add (nvec_to_zvec source)
          (nvec_to_zvec
            (nvec_rsum (Vector.to_list (Vector.map witness_value side_witnesses))))))
      with (nvec_to_zvec target).
    + apply zvec_to_nvec_of_nvec.
    + rewrite zvec_add_assoc,
        (zvec_add_comm_witness (action_offset (action_at rule_index))
          (nvec_to_zvec source)), <- zvec_add_assoc, Heq.
      exact (step_action_equation d source target).
  - apply step_equation_action.
    assert (Hraw :
      zvec_add (action_offset (action_at rule_index))
        (zvec_add (nvec_to_zvec source)
          (nvec_to_zvec
            (nvec_rsum (Vector.to_list (Vector.map witness_value side_witnesses))))) =
      nvec_to_zvec target).
    { apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros i j Hij; subst j.
      unfold nvec_to_zvec.
      rewrite (Vector.nth_map Z.of_nat target i i eq_refl).
      eapply zvec_to_nvec_sound; exact Heq. }
    rewrite <- Hraw, zvec_add_assoc,
      (zvec_add_comm_witness (action_offset (action_at rule_index))
        (nvec_to_zvec source)), <- zvec_add_assoc. reflexivity.
Qed.

Lemma bvas_side_step_occurrences : forall source target,
  BVASSideStep source target ->
  exists (rule_index : idx (length (system_actions S)))
    (side_values : list (NVec d)),
    length side_values = Nat.pred (action_arity (action_at rule_index)) /\
    List.Forall (fun value => Reach S value \/ denote code value) side_values.
Proof.
  intros source target [index [values [Hlength [Hall Happly]]]].
  exists index, values. auto.
Qed.

Lemma side_witnesses_complete : forall n (values : list (NVec d)),
  length values = n ->
  List.Forall (fun value => Reach S value \/ denote code value) values ->
  exists witnesses : Vector.t WitnessAlphabet n,
    Vector.to_list (Vector.map witness_value witnesses) = values.
Proof.
  induction n as [|n IH]; intros values Hlength Hall.
  - destruct values; [|discriminate].
    exists (Vector.nil WitnessAlphabet). reflexivity.
  - destruct values as [|value values]; [discriminate|].
    inversion Hlength; subst. inversion Hall; subst.
    destruct (witness_value_complete value H1) as [head Hhead].
    destruct (IH values eq_refl H2) as [tail Htail].
    exists (Vector.cons WitnessAlphabet head (length values) tail). cbn.
    rewrite Hhead. f_equal. exact Htail.
Qed.

Theorem lemma_5_6_bvas_wsvas_step_iff : forall source target,
  BVASSideStep source target <-> WSVASStep (concrete_wsvas) source target.
Proof.
  intros source target. split.
  - intros [index [values [Hlength [Hall Happly]]]].
    destruct (side_witnesses_complete
      (Nat.pred (action_arity (action_at index))) values Hlength Hall)
      as [witnesses Hvalues].
    exists (@existT _ SideWitnesses index witnesses).
    apply (proj2 (concrete_transition_step_apply_iff index witnesses source target)).
    now rewrite Hvalues.
  - intros [[index witnesses] Hstep].
    set (values := Vector.to_list (Vector.map witness_value witnesses)).
    exists index, values. split.
    + unfold values. apply Vector.length_to_list.
    + split.
      * unfold values. rewrite <- Vector.to_list_Forall, Vector.Forall_map.
        apply Vector.Forall_forall. intros witness _.
        apply witness_value_in_union.
      * apply (proj1 (concrete_transition_step_apply_iff
          index witnesses source target)) in Hstep.
        exact Hstep.
Qed.

End WitnessAlphabet.
