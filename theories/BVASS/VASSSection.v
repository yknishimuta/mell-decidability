From Coq Require Import List Vector VectorSpec Arith ZArith Lia Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.BVASS Require Import Stateful.
From Mell.Reduction Require Import StateErasure.
From Mell.VAS Require Import Runs StatefulVAS.

Import ListNotations.

(** A section keeps the original [d] visible coordinates first.  Acceptance
    names one internal control state for every original state and requires the
    entire auxiliary suffix to be zero. *)
Record VASSSection (d q : nat) : Type := {
  section_aux_dimension : nat;
  section_state_count : nat;
  section_system : VAS (d + section_aux_dimension) section_state_count;
  section_initial_configs :
    list (Mell.VAS.StatefulVAS.SConfig
      (d + section_aux_dimension) section_state_count);
  section_accept_state : Fin.t q -> Fin.t section_state_count
}.

Arguments section_aux_dimension {d q} _.
Arguments section_state_count {d q} _.
Arguments section_system {d q} _.
Arguments section_initial_configs {d q} _.
Arguments section_accept_state {d q} _ _.

Definition section_target_vector {d q} (W : VASSSection d q)
    (counters : NVec d) :
    NVec (d + section_aux_dimension W) :=
  Vector.append counters (nvec_zero (section_aux_dimension W)).

Definition VASSSectionReach {d q} (W : VASSSection d q)
    (state : Fin.t q) (counters : NVec d) : Prop :=
  exists initial_state initial_counters,
    List.In (initial_state, initial_counters) (section_initial_configs W) /\
    VASReach (section_system W)
      initial_state initial_counters
      (section_accept_state W state) (section_target_vector W counters).

Definition empty_vass_section (d q : nat) : VASSSection d q :=
  {| section_aux_dimension := 1;
     section_state_count := q;
     section_system := [];
     section_initial_configs := [];
     section_accept_state := fun state => state |}.

Definition embed_visible {d} (counters : NVec d) : NVec (d + 1) :=
  Vector.append counters (nvec_zero 1).

Definition initial_vass_section {d q}
    (initials : list (Mell.BVASS.Stateful.SConfig d q)) :
    VASSSection d q :=
  {| section_aux_dimension := 1;
     section_state_count := q;
     section_system := [];
     section_initial_configs :=
       List.map (fun config => (fst config, embed_visible (snd config))) initials;
     section_accept_state := fun state => state |}.

Lemma direct_vas_reach_empty_iff : forall d q
    (source_state target_state : Fin.t q)
    (source target : NVec d),
    DirectVASReach [] source_state source target_state target <->
      source_state = target_state /\ source = target.
Proof.
  intros d q source_state target_state source target. split.
  - intro H. inversion H; subst; auto. contradiction.
  - intros [-> ->]. constructor.
Qed.

Theorem empty_vass_section_reach : forall d q state counters,
    ~ VASSSectionReach (empty_vass_section d q) state counters.
Proof.
  intros d q state counters [initial_state [initial_counters [Hin _]]].
  exact Hin.
Qed.

Theorem initial_vass_section_reach_iff : forall d q
    (initials : list (Mell.BVASS.Stateful.SConfig d q))
    (state : Fin.t q) (counters : NVec d),
    VASSSectionReach (initial_vass_section initials) state counters <->
    List.In (state, counters) initials.
Proof.
  intros d q initials state counters. split.
  - intros [initial_state [initial_counters [Hin Hreach]]].
    apply List.in_map_iff in Hin as [[listed_state listed_counters]
      [Hconfig Hin]]. cbn in Hconfig.
    injection Hconfig as Hstate0 Hcounter0.
    subst initial_state initial_counters. cbn in Hreach.
    apply vas_reach_direct_iff in Hreach.
    apply direct_vas_reach_empty_iff in Hreach as [Hstate Hcounters].
    cbn in Hstate. subst listed_state.
    unfold section_target_vector in Hcounters; cbn in Hcounters.
    apply Vector.append_inj in Hcounters as [Hvisible _].
    subst listed_counters.
    exact Hin.
  - intro Hin. exists state, (embed_visible counters). split.
    + apply List.in_map_iff. exists (state, counters). split; [reflexivity|exact Hin].
    + apply vas_reach_direct_iff. constructor.
Qed.

(** Finite disjoint union. *)
Fixpoint all_fin (n : nat) : list (Fin.t n) :=
  match n with
  | O => []
  | S n' => Fin.F1 :: List.map Fin.FS (all_fin n')
  end.

Lemma all_fin_complete : forall n (index : Fin.t n),
    List.In index (all_fin n).
Proof.
  induction n as [|n IH]; intro index.
  - exact (Fin.case0 (fun index => List.In index (all_fin 0)) index).
  - refine (Fin.caseS' index
      (fun selected => List.In selected (all_fin (S n))) _ _).
    + cbn. auto.
    + intro tail. cbn. right. apply List.in_map. apply IH.
Qed.

Definition section_left_state {d q} (W1 W2 : VASSSection d q)
    (state : Fin.t (section_state_count W1)) :
    Fin.t (section_state_count W1 + (section_state_count W2 + q)) :=
  Fin.L (section_state_count W2 + q) state.

Definition section_right_state {d q} (W1 W2 : VASSSection d q)
    (state : Fin.t (section_state_count W2)) :
    Fin.t (section_state_count W1 + (section_state_count W2 + q)) :=
  Fin.R (section_state_count W1) (Fin.L q state).

Definition section_union_accept {d q} (W1 W2 : VASSSection d q)
    (state : Fin.t q) :
    Fin.t (section_state_count W1 + (section_state_count W2 + q)) :=
  Fin.R (section_state_count W1) (Fin.R (section_state_count W2) state).

Definition split_visible_n {d auxiliary} (value : NVec (d + auxiliary)) :=
  Vector.splitat d value.

Definition split_visible_z {d auxiliary} (value : ZVec (d + auxiliary)) :=
  Vector.splitat d value.

Definition section_left_nvec {d q} (W1 W2 : VASSSection d q)
    (value : NVec (d + section_aux_dimension W1)) :
    NVec (d + (section_aux_dimension W1 + section_aux_dimension W2)) :=
  let parts := split_visible_n value in
  Vector.append (fst parts)
    (Vector.append (snd parts) (nvec_zero (section_aux_dimension W2))).

Definition section_right_nvec {d q} (W1 W2 : VASSSection d q)
    (value : NVec (d + section_aux_dimension W2)) :
    NVec (d + (section_aux_dimension W1 + section_aux_dimension W2)) :=
  let parts := split_visible_n value in
  Vector.append (fst parts)
    (Vector.append (nvec_zero (section_aux_dimension W1)) (snd parts)).

Definition section_left_zvec {d q} (W1 W2 : VASSSection d q)
    (value : ZVec (d + section_aux_dimension W1)) :
    ZVec (d + (section_aux_dimension W1 + section_aux_dimension W2)) :=
  let parts := split_visible_z value in
  Vector.append (fst parts)
    (Vector.append (snd parts) (zvec_zero (section_aux_dimension W2))).

Definition section_right_zvec {d q} (W1 W2 : VASSSection d q)
    (value : ZVec (d + section_aux_dimension W2)) :
    ZVec (d + (section_aux_dimension W1 + section_aux_dimension W2)) :=
  let parts := split_visible_z value in
  Vector.append (fst parts)
    (Vector.append (zvec_zero (section_aux_dimension W1)) (snd parts)).

Definition section_left_transition {d q} (W1 W2 : VASSSection d q)
    (transition : VASTransition
      (d + section_aux_dimension W1) (section_state_count W1)) :
    VASTransition
      (d + (section_aux_dimension W1 + section_aux_dimension W2))
      (section_state_count W1 + (section_state_count W2 + q)) :=
  {| VASTransitionSource := section_left_state W1 W2
       (VASTransitionSource transition);
     VASTransitionAction := section_left_zvec W1 W2
       (VASTransitionAction transition);
     VASTransitionTarget := section_left_state W1 W2
       (VASTransitionTarget transition) |}.

Definition section_right_transition {d q} (W1 W2 : VASSSection d q)
    (transition : VASTransition
      (d + section_aux_dimension W2) (section_state_count W2)) :
    VASTransition
      (d + (section_aux_dimension W1 + section_aux_dimension W2))
      (section_state_count W1 + (section_state_count W2 + q)) :=
  {| VASTransitionSource := section_right_state W1 W2
       (VASTransitionSource transition);
     VASTransitionAction := section_right_zvec W1 W2
       (VASTransitionAction transition);
     VASTransitionTarget := section_right_state W1 W2
       (VASTransitionTarget transition) |}.

Definition section_left_exit {d q} (W1 W2 : VASSSection d q)
    (state : Fin.t q) :
    VASTransition
      (d + (section_aux_dimension W1 + section_aux_dimension W2))
      (section_state_count W1 + (section_state_count W2 + q)) :=
  {| VASTransitionSource := section_left_state W1 W2
       (section_accept_state W1 state);
     VASTransitionAction :=
       zvec_zero (d + (section_aux_dimension W1 + section_aux_dimension W2));
     VASTransitionTarget := section_union_accept W1 W2 state |}.

Definition section_right_exit {d q} (W1 W2 : VASSSection d q)
    (state : Fin.t q) :
    VASTransition
      (d + (section_aux_dimension W1 + section_aux_dimension W2))
      (section_state_count W1 + (section_state_count W2 + q)) :=
  {| VASTransitionSource := section_right_state W1 W2
       (section_accept_state W2 state);
     VASTransitionAction :=
       zvec_zero (d + (section_aux_dimension W1 + section_aux_dimension W2));
     VASTransitionTarget := section_union_accept W1 W2 state |}.

Definition section_union_system {d q} (W1 W2 : VASSSection d q) :=
  List.map (section_left_transition W1 W2) (section_system W1) ++
  List.map (section_right_transition W1 W2) (section_system W2) ++
  List.map (section_left_exit W1 W2) (all_fin q) ++
  List.map (section_right_exit W1 W2) (all_fin q).

Definition section_left_initial {d q} (W1 W2 : VASSSection d q)
    (config : Mell.VAS.StatefulVAS.SConfig
      (d + section_aux_dimension W1) (section_state_count W1)) :=
  (section_left_state W1 W2 (fst config), section_left_nvec W1 W2 (snd config)).

Definition section_right_initial {d q} (W1 W2 : VASSSection d q)
    (config : Mell.VAS.StatefulVAS.SConfig
      (d + section_aux_dimension W2) (section_state_count W2)) :=
  (section_right_state W1 W2 (fst config), section_right_nvec W1 W2 (snd config)).

Definition vass_section_union {d q} (W1 W2 : VASSSection d q) :
    VASSSection d q :=
  {| section_aux_dimension :=
       section_aux_dimension W1 + section_aux_dimension W2;
     section_state_count :=
       section_state_count W1 + (section_state_count W2 + q);
     section_system := section_union_system W1 W2;
     section_initial_configs :=
       List.map (section_left_initial W1 W2) (section_initial_configs W1) ++
       List.map (section_right_initial W1 W2) (section_initial_configs W2);
     section_accept_state := section_union_accept W1 W2 |}.

Lemma vector_map2_append_section : forall A B C (operation : A -> B -> C)
    left_length right_length
    (left1 : Vector.t A left_length) (right1 : Vector.t A right_length)
    (left2 : Vector.t B left_length) (right2 : Vector.t B right_length),
    Vector.map2 operation (Vector.append left1 right1)
      (Vector.append left2 right2) =
    Vector.append (Vector.map2 operation left1 left2)
      (Vector.map2 operation right1 right2).
Proof.
  intros A B C operation left_length right_length left1.
  induction left1 as [|head length tail IH]; intros right1 left2 right2.
  - refine (Vector.case0 (fun left2 => _) _ left2). reflexivity.
  - refine (Vector.caseS' left2 (fun left2 => _) _).
    intros head2 tail2. cbn. f_equal. apply IH.
Qed.

Lemma step_action_append : forall left right
    (source_left target_left : NVec left)
    (source_right target_right : NVec right),
    StepAction (Vector.append source_left source_right)
      (Vector.append target_left target_right) =
    Vector.append (StepAction source_left target_left)
      (StepAction source_right target_right).
Proof.
  intros. unfold StepAction, zvec_sub_run.
  rewrite !nvec_to_zvec_append.
  apply vector_map2_append_section.
Qed.

Lemma step_action_zero : forall d,
    StepAction (nvec_zero d) (nvec_zero d) = zvec_zero d.
Proof.
  intros d. unfold StepAction, zvec_sub_run, nvec_zero, nvec_to_zvec,
    zvec_zero. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'.
  rewrite (nth_map2 Z.sub _ _ index index index eq_refl eq_refl).
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl).
  repeat rewrite const_nth. lia.
Qed.

Lemma section_left_nvec_append : forall d q (W1 W2 : VASSSection d q)
    (visible : NVec d) (auxiliary : NVec (section_aux_dimension W1)),
    section_left_nvec W1 W2 (Vector.append visible auxiliary) =
    Vector.append visible
      (Vector.append auxiliary (nvec_zero (section_aux_dimension W2))).
Proof.
  intros. unfold section_left_nvec, split_visible_n.
  now rewrite VectorSpec.splitat_append.
Qed.

Lemma section_right_nvec_append : forall d q (W1 W2 : VASSSection d q)
    (visible : NVec d) (auxiliary : NVec (section_aux_dimension W2)),
    section_right_nvec W1 W2 (Vector.append visible auxiliary) =
    Vector.append visible
      (Vector.append (nvec_zero (section_aux_dimension W1)) auxiliary).
Proof.
  intros. unfold section_right_nvec, split_visible_n.
  now rewrite VectorSpec.splitat_append.
Qed.

Lemma section_left_zvec_append : forall d q (W1 W2 : VASSSection d q)
    (visible : ZVec d) (auxiliary : ZVec (section_aux_dimension W1)),
    section_left_zvec W1 W2 (Vector.append visible auxiliary) =
    Vector.append visible
      (Vector.append auxiliary (zvec_zero (section_aux_dimension W2))).
Proof.
  intros. unfold section_left_zvec, split_visible_z.
  now rewrite VectorSpec.splitat_append.
Qed.

Lemma section_right_zvec_append : forall d q (W1 W2 : VASSSection d q)
    (visible : ZVec d) (auxiliary : ZVec (section_aux_dimension W2)),
    section_right_zvec W1 W2 (Vector.append visible auxiliary) =
    Vector.append visible
      (Vector.append (zvec_zero (section_aux_dimension W1)) auxiliary).
Proof.
  intros. unfold section_right_zvec, split_visible_z.
  now rewrite VectorSpec.splitat_append.
Qed.

Lemma section_left_step_action : forall d q (W1 W2 : VASSSection d q)
    source target,
    section_left_zvec W1 W2 (StepAction source target) =
    StepAction (section_left_nvec W1 W2 source)
      (section_left_nvec W1 W2 target).
Proof.
  intros d q W1 W2 source target.
  destruct (Vector.splitat d source) as [source_visible source_aux] eqn:Hsource.
  destruct (Vector.splitat d target) as [target_visible target_aux] eqn:Htarget.
  apply VectorSpec.append_splitat in Hsource.
  apply VectorSpec.append_splitat in Htarget. subst source target.
  rewrite step_action_append, section_left_zvec_append.
  rewrite !section_left_nvec_append.
  rewrite step_action_append, step_action_append, step_action_zero.
  reflexivity.
Qed.

Lemma section_right_step_action : forall d q (W1 W2 : VASSSection d q)
    source target,
    section_right_zvec W1 W2 (StepAction source target) =
    StepAction (section_right_nvec W1 W2 source)
      (section_right_nvec W1 W2 target).
Proof.
  intros d q W1 W2 source target.
  destruct (Vector.splitat d source) as [source_visible source_aux] eqn:Hsource.
  destruct (Vector.splitat d target) as [target_visible target_aux] eqn:Htarget.
  apply VectorSpec.append_splitat in Hsource.
  apply VectorSpec.append_splitat in Htarget. subst source target.
  rewrite step_action_append, section_right_zvec_append.
  rewrite !section_right_nvec_append.
  rewrite step_action_append, step_action_append, step_action_zero.
  reflexivity.
Qed.

Lemma section_left_transition_in : forall d q (W1 W2 : VASSSection d q)
    transition,
    List.In transition (section_system W1) ->
    List.In (section_left_transition W1 W2 transition)
      (section_union_system W1 W2).
Proof.
  intros. unfold section_union_system.
  apply in_or_app. left. now apply List.in_map.
Qed.

Lemma section_right_transition_in : forall d q (W1 W2 : VASSSection d q)
    transition,
    List.In transition (section_system W2) ->
    List.In (section_right_transition W1 W2 transition)
      (section_union_system W1 W2).
Proof.
  intros. unfold section_union_system.
  apply in_or_app. right. apply in_or_app. left. now apply List.in_map.
Qed.

Lemma section_left_direct_reach : forall d q (W1 W2 : VASSSection d q)
    source_state source target_state target,
    DirectVASReach (section_system W1) source_state source target_state target ->
    DirectVASReach (section_union_system W1 W2)
      (section_left_state W1 W2 source_state) (section_left_nvec W1 W2 source)
      (section_left_state W1 W2 target_state) (section_left_nvec W1 W2 target).
Proof.
  intros d q W1 W2 source_state source target_state target Hreach.
  induction Hreach.
  - constructor.
  - eapply direct_vas_reach_step with
      (transition := section_left_transition W1 W2 transition)
      (target := section_left_nvec W1 W2 target).
    + now apply section_left_transition_in.
    + cbn. rewrite H0. apply section_left_step_action.
    + exact IHHreach.
Qed.

Lemma section_right_direct_reach : forall d q (W1 W2 : VASSSection d q)
    source_state source target_state target,
    DirectVASReach (section_system W2) source_state source target_state target ->
    DirectVASReach (section_union_system W1 W2)
      (section_right_state W1 W2 source_state) (section_right_nvec W1 W2 source)
      (section_right_state W1 W2 target_state) (section_right_nvec W1 W2 target).
Proof.
  intros d q W1 W2 source_state source target_state target Hreach.
  induction Hreach.
  - constructor.
  - eapply direct_vas_reach_step with
      (transition := section_right_transition W1 W2 transition)
      (target := section_right_nvec W1 W2 target).
    + now apply section_right_transition_in.
    + cbn. rewrite H0. apply section_right_step_action.
    + exact IHHreach.
Qed.

Lemma direct_vas_reach_trans : forall d q (system : VAS d q)
    source_state source middle_state middle target_state target,
    DirectVASReach system source_state source middle_state middle ->
    DirectVASReach system middle_state middle target_state target ->
    DirectVASReach system source_state source target_state target.
Proof.
  intros d q system source_state source middle_state middle target_state target
    Hleft Hright. induction Hleft.
  - exact Hright.
  - econstructor; eauto.
Qed.

Lemma step_action_refl : forall d (value : NVec d),
    StepAction value value = zvec_zero d.
Proof.
  intros d value. unfold StepAction, zvec_sub_run, zvec_zero.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'.
  rewrite (nth_map2 Z.sub _ _ index index index eq_refl eq_refl).
  rewrite const_nth. lia.
Qed.

Lemma section_left_target : forall d q (W1 W2 : VASSSection d q) counters,
    section_left_nvec W1 W2 (section_target_vector W1 counters) =
    section_target_vector (vass_section_union W1 W2) counters.
Proof.
  intros. unfold section_target_vector.
  rewrite section_left_nvec_append, <- nvec_zero_append. reflexivity.
Qed.

Lemma section_right_target : forall d q (W1 W2 : VASSSection d q) counters,
    section_right_nvec W1 W2 (section_target_vector W2 counters) =
    section_target_vector (vass_section_union W1 W2) counters.
Proof.
  intros. unfold section_target_vector.
  rewrite section_right_nvec_append, <- nvec_zero_append. reflexivity.
Qed.

Lemma section_left_exit_in : forall d q (W1 W2 : VASSSection d q) state,
    List.In (section_left_exit W1 W2 state) (section_union_system W1 W2).
Proof.
  intros. unfold section_union_system.
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  apply List.in_map. apply all_fin_complete.
Qed.

Lemma section_right_exit_in : forall d q (W1 W2 : VASSSection d q) state,
    List.In (section_right_exit W1 W2 state) (section_union_system W1 W2).
Proof.
  intros. unfold section_union_system.
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
  apply List.in_map. apply all_fin_complete.
Qed.

Lemma section_left_exit_reach : forall d q (W1 W2 : VASSSection d q)
    state value,
    DirectVASReach (section_union_system W1 W2)
      (section_left_state W1 W2 (section_accept_state W1 state)) value
      (section_union_accept W1 W2 state) value.
Proof.
  intros. eapply direct_vas_reach_step with
      (transition := section_left_exit W1 W2 state) (target := value).
  - apply section_left_exit_in.
  - cbn. symmetry. apply step_action_refl.
  - constructor.
Qed.

Lemma section_right_exit_reach : forall d q (W1 W2 : VASSSection d q)
    state value,
    DirectVASReach (section_union_system W1 W2)
      (section_right_state W1 W2 (section_accept_state W2 state)) value
      (section_union_accept W1 W2 state) value.
Proof.
  intros. eapply direct_vas_reach_step with
      (transition := section_right_exit W1 W2 state) (target := value).
  - apply section_right_exit_in.
  - cbn. symmetry. apply step_action_refl.
  - constructor.
Qed.

Theorem vass_section_union_complete : forall d q (W1 W2 : VASSSection d q)
    state counters,
    VASSSectionReach W1 state counters \/ VASSSectionReach W2 state counters ->
    VASSSectionReach (vass_section_union W1 W2) state counters.
Proof.
  intros d q W1 W2 state counters [Hleft|Hright].
  - destruct Hleft as [initial_state [initial_counters [Hinitial Hreach]]].
    exists (section_left_state W1 W2 initial_state),
      (section_left_nvec W1 W2 initial_counters). split.
    + apply in_or_app. left. apply List.in_map_iff.
      exists (initial_state, initial_counters). split; [reflexivity|exact Hinitial].
    + apply vas_reach_direct_iff in Hreach.
      apply vas_reach_direct_iff.
      eapply direct_vas_reach_trans.
      * exact (section_left_direct_reach d q W1 W2 _ _ _ _ Hreach).
      * rewrite section_left_target.
        apply section_left_exit_reach.
  - destruct Hright as [initial_state [initial_counters [Hinitial Hreach]]].
    exists (section_right_state W1 W2 initial_state),
      (section_right_nvec W1 W2 initial_counters). split.
    + apply in_or_app. right. apply List.in_map_iff.
      exists (initial_state, initial_counters). split; [reflexivity|exact Hinitial].
    + apply vas_reach_direct_iff in Hreach.
      apply vas_reach_direct_iff.
      eapply direct_vas_reach_trans.
      * exact (section_right_direct_reach d q W1 W2 _ _ _ _ Hreach).
      * rewrite section_right_target.
        apply section_right_exit_reach.
Qed.

Lemma fin_left_injective : forall left right (x y : Fin.t left),
    Fin.L right x = Fin.L right y -> x = y.
Proof.
  intros. now apply Fin.L_inj in H.
Qed.

Lemma fin_right_injective : forall left right (x y : Fin.t right),
    Fin.R left x = Fin.R left y -> x = y.
Proof.
  intros. now apply Fin.R_inj in H.
Qed.

Lemma fin_left_right_distinct : forall left right
    (x : Fin.t left) (y : Fin.t right),
    Fin.L right x <> Fin.R left y.
Proof.
  intros. apply Fin.L_R_neq.
Qed.

Lemma section_left_state_injective : forall d q (W1 W2 : VASSSection d q)
    (x y : Fin.t (section_state_count W1)),
    section_left_state W1 W2 x = section_left_state W1 W2 y -> x = y.
Proof.
  intros d q W1 W2 x y Heq. unfold section_left_state in Heq.
  now apply Fin.L_inj in Heq.
Qed.

Lemma section_right_state_injective : forall d q (W1 W2 : VASSSection d q)
    (x y : Fin.t (section_state_count W2)),
    section_right_state W1 W2 x = section_right_state W1 W2 y -> x = y.
Proof.
  intros d q W1 W2 x y Heq. unfold section_right_state in Heq.
  apply Fin.R_inj in Heq. now apply Fin.L_inj in Heq.
Qed.

Lemma section_left_right_distinct : forall d q (W1 W2 : VASSSection d q)
    (x : Fin.t (section_state_count W1))
    (y : Fin.t (section_state_count W2)),
    section_left_state W1 W2 x <> section_right_state W1 W2 y.
Proof.
  intros. unfold section_left_state, section_right_state.
  apply fin_left_right_distinct.
Qed.

Lemma section_left_accept_distinct : forall d q (W1 W2 : VASSSection d q)
    (x : Fin.t (section_state_count W1)) (state : Fin.t q),
    section_left_state W1 W2 x <> section_union_accept W1 W2 state.
Proof.
  intros. unfold section_left_state, section_union_accept.
  apply fin_left_right_distinct.
Qed.

Lemma section_right_accept_distinct : forall d q (W1 W2 : VASSSection d q)
    (x : Fin.t (section_state_count W2)) (state : Fin.t q),
    section_right_state W1 W2 x <> section_union_accept W1 W2 state.
Proof.
  intros d q W1 W2 x state Heq. unfold section_right_state,
    section_union_accept in Heq. apply Fin.R_inj in Heq.
  now apply fin_left_right_distinct in Heq.
Qed.

Lemma section_union_accept_injective : forall d q (W1 W2 : VASSSection d q)
    (x y : Fin.t q),
    section_union_accept W1 W2 x = section_union_accept W1 W2 y -> x = y.
Proof.
  intros d q W1 W2 x y Heq. unfold section_union_accept in Heq.
  apply Fin.R_inj in Heq. now apply Fin.R_inj in Heq.
Qed.

Lemma section_union_transition_cases : forall d q
    (W1 W2 : VASSSection d q) transition,
    List.In transition (section_union_system W1 W2) ->
    (exists original,
      List.In original (section_system W1) /\
      transition = section_left_transition W1 W2 original) \/
    (exists original,
      List.In original (section_system W2) /\
      transition = section_right_transition W1 W2 original) \/
    (exists state, transition = section_left_exit W1 W2 state) \/
    (exists state, transition = section_right_exit W1 W2 state).
Proof.
  intros d q W1 W2 transition Hin. unfold section_union_system in Hin.
  repeat rewrite in_app_iff in Hin.
  destruct Hin as [Hin|[Hin|[Hin|Hin]]].
  - left. apply List.in_map_iff in Hin as [original [<- Hin]]. eauto.
  - right; left. apply List.in_map_iff in Hin as [original [<- Hin]]. eauto.
  - right; right; left.
    apply List.in_map_iff in Hin as [state [<- _]]. eauto.
  - right; right; right.
    apply List.in_map_iff in Hin as [state [<- _]]. eauto.
Qed.

Lemma union_accept_has_no_step : forall d q (W1 W2 : VASSSection d q)
    state transition,
    List.In transition (section_union_system W1 W2) ->
    VASTransitionSource transition = section_union_accept W1 W2 state -> False.
Proof.
  intros d q W1 W2 state transition Hin Hsource.
  destruct (section_union_transition_cases d q W1 W2 transition Hin)
    as [[original [_ ->]]|[[original [_ ->]]|[[selected ->]|[selected ->]]]];
    cbn in Hsource.
  - exact (section_left_accept_distinct d q W1 W2
      (VASTransitionSource original) state Hsource).
  - exact (section_right_accept_distinct d q W1 W2
      (VASTransitionSource original) state Hsource).
  - exact (section_left_accept_distinct d q W1 W2
      (section_accept_state W1 selected) state Hsource).
  - exact (section_right_accept_distinct d q W1 W2
      (section_accept_state W2 selected) state Hsource).
Qed.

Lemma union_accept_reach_inv : forall d q (W1 W2 : VASSSection d q)
    state counters target_state target,
    DirectVASReach (section_union_system W1 W2)
      (section_union_accept W1 W2 state) counters target_state target ->
    target_state = section_union_accept W1 W2 state /\ target = counters.
Proof.
  intros d q W1 W2 state counters target_state target Hreach.
  inversion Hreach; subst; [auto|].
  exfalso. eapply union_accept_has_no_step; eauto.
Qed.

Definition section_left_project_nvec {d q} (W1 W2 : VASSSection d q)
    (value : NVec (d + (section_aux_dimension W1 + section_aux_dimension W2)))
    : NVec (d + section_aux_dimension W1) :=
  let outer := Vector.splitat d value in
  let auxiliary := Vector.splitat (section_aux_dimension W1) (snd outer) in
  Vector.append (fst outer) (fst auxiliary).

Definition section_right_project_nvec {d q} (W1 W2 : VASSSection d q)
    (value : NVec (d + (section_aux_dimension W1 + section_aux_dimension W2)))
    : NVec (d + section_aux_dimension W2) :=
  let outer := Vector.splitat d value in
  let auxiliary := Vector.splitat (section_aux_dimension W1) (snd outer) in
  Vector.append (fst outer) (snd auxiliary).

Definition section_left_project_zvec {d q} (W1 W2 : VASSSection d q)
    (value : ZVec (d + (section_aux_dimension W1 + section_aux_dimension W2)))
    : ZVec (d + section_aux_dimension W1) :=
  let outer := Vector.splitat d value in
  let auxiliary := Vector.splitat (section_aux_dimension W1) (snd outer) in
  Vector.append (fst outer) (fst auxiliary).

Definition section_right_project_zvec {d q} (W1 W2 : VASSSection d q)
    (value : ZVec (d + (section_aux_dimension W1 + section_aux_dimension W2)))
    : ZVec (d + section_aux_dimension W2) :=
  let outer := Vector.splitat d value in
  let auxiliary := Vector.splitat (section_aux_dimension W1) (snd outer) in
  Vector.append (fst outer) (snd auxiliary).

Lemma section_left_project_lift_nvec : forall d q
    (W1 W2 : VASSSection d q) value,
    section_left_project_nvec W1 W2 (section_left_nvec W1 W2 value) = value.
Proof.
  intros d q W1 W2 value.
  destruct (Vector.splitat d value) as [visible auxiliary] eqn:Hsplit.
  apply VectorSpec.append_splitat in Hsplit. subst value.
  rewrite section_left_nvec_append.
  unfold section_left_project_nvec.
  rewrite VectorSpec.splitat_append. cbn.
  rewrite VectorSpec.splitat_append. reflexivity.
Qed.

Lemma section_right_project_lift_nvec : forall d q
    (W1 W2 : VASSSection d q) value,
    section_right_project_nvec W1 W2 (section_right_nvec W1 W2 value) = value.
Proof.
  intros d q W1 W2 value.
  destruct (Vector.splitat d value) as [visible auxiliary] eqn:Hsplit.
  apply VectorSpec.append_splitat in Hsplit. subst value.
  rewrite section_right_nvec_append.
  unfold section_right_project_nvec.
  rewrite VectorSpec.splitat_append. cbn.
  rewrite VectorSpec.splitat_append. reflexivity.
Qed.

Lemma section_left_project_lift_zvec : forall d q
    (W1 W2 : VASSSection d q) value,
    section_left_project_zvec W1 W2 (section_left_zvec W1 W2 value) = value.
Proof.
  intros d q W1 W2 value.
  destruct (Vector.splitat d value) as [visible auxiliary] eqn:Hsplit.
  apply VectorSpec.append_splitat in Hsplit. subst value.
  rewrite section_left_zvec_append.
  unfold section_left_project_zvec.
  rewrite VectorSpec.splitat_append. cbn.
  rewrite VectorSpec.splitat_append. reflexivity.
Qed.

Lemma section_right_project_lift_zvec : forall d q
    (W1 W2 : VASSSection d q) value,
    section_right_project_zvec W1 W2 (section_right_zvec W1 W2 value) = value.
Proof.
  intros d q W1 W2 value.
  destruct (Vector.splitat d value) as [visible auxiliary] eqn:Hsplit.
  apply VectorSpec.append_splitat in Hsplit. subst value.
  rewrite section_right_zvec_append.
  unfold section_right_project_zvec.
  rewrite VectorSpec.splitat_append. cbn.
  rewrite VectorSpec.splitat_append. reflexivity.
Qed.

Lemma section_left_project_step_action : forall d q
    (W1 W2 : VASSSection d q) source target,
    section_left_project_zvec W1 W2 (StepAction source target) =
    StepAction (section_left_project_nvec W1 W2 source)
      (section_left_project_nvec W1 W2 target).
Proof.
  intros d q W1 W2 source target.
  destruct (Vector.splitat d source) as [sv ss] eqn:Hs.
  destruct (Vector.splitat (section_aux_dimension W1) ss) as [sa sb] eqn:Hss.
  destruct (Vector.splitat d target) as [tv ts] eqn:Ht.
  destruct (Vector.splitat (section_aux_dimension W1) ts) as [ta tb] eqn:Hts.
  apply VectorSpec.append_splitat in Hs, Hss, Ht, Hts.
  subst ss ts source target.
  repeat rewrite step_action_append.
  unfold section_left_project_zvec, section_left_project_nvec.
  repeat rewrite VectorSpec.splitat_append.
  cbn [fst snd].
  repeat rewrite VectorSpec.splitat_append.
  cbn [fst snd].
  repeat rewrite step_action_append. reflexivity.
Qed.

Lemma section_right_project_step_action : forall d q
    (W1 W2 : VASSSection d q) source target,
    section_right_project_zvec W1 W2 (StepAction source target) =
    StepAction (section_right_project_nvec W1 W2 source)
      (section_right_project_nvec W1 W2 target).
Proof.
  intros d q W1 W2 source target.
  destruct (Vector.splitat d source) as [sv ss] eqn:Hs.
  destruct (Vector.splitat (section_aux_dimension W1) ss) as [sa sb] eqn:Hss.
  destruct (Vector.splitat d target) as [tv ts] eqn:Ht.
  destruct (Vector.splitat (section_aux_dimension W1) ts) as [ta tb] eqn:Hts.
  apply VectorSpec.append_splitat in Hs, Hss, Ht, Hts.
  subst ss ts source target.
  repeat rewrite step_action_append.
  unfold section_right_project_zvec, section_right_project_nvec.
  repeat rewrite VectorSpec.splitat_append.
  cbn [fst snd].
  repeat rewrite VectorSpec.splitat_append.
  cbn [fst snd].
  repeat rewrite step_action_append. reflexivity.
Qed.

Lemma section_left_project_target : forall d q
    (W1 W2 : VASSSection d q) counters,
    section_left_project_nvec W1 W2
      (section_target_vector (vass_section_union W1 W2) counters) =
    section_target_vector W1 counters.
Proof.
  intros d q W1 W2 counters.
  rewrite <- (section_left_target d q W1 W2 counters).
  apply section_left_project_lift_nvec.
Qed.

Lemma section_right_project_target : forall d q
    (W1 W2 : VASSSection d q) counters,
    section_right_project_nvec W1 W2
      (section_target_vector (vass_section_union W1 W2) counters) =
    section_target_vector W2 counters.
Proof.
  intros d q W1 W2 counters.
  rewrite <- (section_right_target d q W1 W2 counters).
  apply section_right_project_lift_nvec.
Qed.

Lemma step_action_zero_eq : forall d (source target : NVec d),
    StepAction source target = zvec_zero d -> source = target.
Proof.
  intros d source target Heq.
  apply nvec_to_zvec_inj.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Hindex; subst index'.
  pose proof (f_equal (fun vector => Vector.nth vector index) Heq) as Hcoord.
  unfold StepAction, zvec_sub_run, zvec_zero in Hcoord.
  rewrite (nth_map2 Z.sub _ _ index index index eq_refl eq_refl),
    const_nth in Hcoord. lia.
Qed.

Lemma union_left_phase_decode : forall d q (W1 W2 : VASSSection d q)
    source_state source target_state target,
    DirectVASReach (section_union_system W1 W2)
      source_state source target_state target ->
    forall original_source final_state,
      source_state = section_left_state W1 W2 original_source ->
      target_state = section_union_accept W1 W2 final_state ->
      DirectVASReach (section_system W1)
        original_source (section_left_project_nvec W1 W2 source)
        (section_accept_state W1 final_state)
        (section_left_project_nvec W1 W2 target).
Proof.
  intros d q W1 W2 source_state source target_state target Hreach.
  induction Hreach as
      [state counters|transition step_source step_target final_state final
        Hin Haction Htail IH];
    intros original_source selected Hsource Hfinal.
  - exfalso. subst state.
    eapply section_left_accept_distinct; exact Hfinal.
  - destruct (section_union_transition_cases d q W1 W2 transition Hin)
      as [[original [Horiginal ->]]|
          [[original [Horiginal ->]]|
           [[exit_state ->]|[exit_state ->]]]].
    + cbn in Hsource, Haction.
      apply section_left_state_injective in Hsource. subst original_source.
      eapply direct_vas_reach_step with (transition := original)
          (target := section_left_project_nvec W1 W2 step_target).
      * exact Horiginal.
      * pose proof (f_equal (section_left_project_zvec W1 W2) Haction)
          as Hproject.
        rewrite section_left_project_lift_zvec,
          section_left_project_step_action in Hproject. exact Hproject.
      * eapply IH; [reflexivity|exact Hfinal].
    + exfalso. cbn in Hsource.
      apply (section_left_right_distinct d q W1 W2 original_source
        (VASTransitionSource original)). now symmetry.
    + cbn in Hsource, Haction.
      apply section_left_state_injective in Hsource. subst original_source.
      assert (Hcounter : step_source = step_target).
      { apply step_action_zero_eq. now symmetry. }
      destruct (union_accept_reach_inv d q W1 W2 exit_state step_target
        final_state final Htail) as [Hstate Htarget].
      assert (Hselected : exit_state = selected).
      { apply (section_union_accept_injective d q W1 W2).
        now rewrite <- Hstate, <- Hfinal. }
      subst selected.
      subst final step_target. constructor.
    + exfalso. cbn in Hsource.
      apply (section_left_right_distinct d q W1 W2 original_source
        (section_accept_state W2 exit_state)). now symmetry.
Qed.

Lemma union_right_phase_decode : forall d q (W1 W2 : VASSSection d q)
    source_state source target_state target,
    DirectVASReach (section_union_system W1 W2)
      source_state source target_state target ->
    forall original_source final_state,
      source_state = section_right_state W1 W2 original_source ->
      target_state = section_union_accept W1 W2 final_state ->
      DirectVASReach (section_system W2)
        original_source (section_right_project_nvec W1 W2 source)
        (section_accept_state W2 final_state)
        (section_right_project_nvec W1 W2 target).
Proof.
  intros d q W1 W2 source_state source target_state target Hreach.
  induction Hreach as
      [state counters|transition step_source step_target final_state final
        Hin Haction Htail IH];
    intros original_source selected Hsource Hfinal.
  - exfalso. subst state.
    eapply section_right_accept_distinct; exact Hfinal.
  - destruct (section_union_transition_cases d q W1 W2 transition Hin)
      as [[original [Horiginal ->]]|
          [[original [Horiginal ->]]|
           [[exit_state ->]|[exit_state ->]]]].
    + exfalso. cbn in Hsource.
      apply (section_left_right_distinct d q W1 W2
        (VASTransitionSource original) original_source).
      now symmetry.
    + cbn in Hsource, Haction.
      apply section_right_state_injective in Hsource. subst original_source.
      eapply direct_vas_reach_step with (transition := original)
          (target := section_right_project_nvec W1 W2 step_target).
      * exact Horiginal.
      * pose proof (f_equal (section_right_project_zvec W1 W2) Haction)
          as Hproject.
        rewrite section_right_project_lift_zvec,
          section_right_project_step_action in Hproject. exact Hproject.
      * eapply IH; [reflexivity|exact Hfinal].
    + exfalso. cbn in Hsource.
      apply (section_left_right_distinct d q W1 W2
        (section_accept_state W1 exit_state) original_source).
      now symmetry.
    + cbn in Hsource, Haction.
      apply section_right_state_injective in Hsource. subst original_source.
      assert (Hcounter : step_source = step_target).
      { apply step_action_zero_eq. now symmetry. }
      destruct (union_accept_reach_inv d q W1 W2 exit_state step_target
        final_state final Htail) as [Hstate Htarget].
      assert (Hselected : exit_state = selected).
      { apply (section_union_accept_injective d q W1 W2).
        now rewrite <- Hstate, <- Hfinal. }
      subst selected.
      subst final step_target. constructor.
Qed.

Theorem vass_section_union_sound : forall d q (W1 W2 : VASSSection d q)
    state counters,
    VASSSectionReach (vass_section_union W1 W2) state counters ->
    VASSSectionReach W1 state counters \/ VASSSectionReach W2 state counters.
Proof.
  intros d q W1 W2 state counters
    [initial_state [initial_counters [Hinitial Hreach]]].
  unfold vass_section_union in Hinitial; cbn in Hinitial.
  apply in_app_iff in Hinitial as [Hleft|Hright].
  - apply List.in_map_iff in Hleft as [[source_state source] [Hconfig Hin]].
    cbn in Hconfig. inversion Hconfig; subst initial_state initial_counters.
    left. exists source_state, source. split; [exact Hin|].
    apply vas_reach_direct_iff in Hreach. apply vas_reach_direct_iff.
    pose proof (union_left_phase_decode d q W1 W2 _ _ _ _ Hreach
      source_state state eq_refl eq_refl) as Hdecoded.
    rewrite section_left_project_lift_nvec,
      section_left_project_target in Hdecoded. exact Hdecoded.
  - apply List.in_map_iff in Hright as [[source_state source] [Hconfig Hin]].
    cbn in Hconfig. inversion Hconfig; subst initial_state initial_counters.
    right. exists source_state, source. split; [exact Hin|].
    apply vas_reach_direct_iff in Hreach. apply vas_reach_direct_iff.
    pose proof (union_right_phase_decode d q W1 W2 _ _ _ _ Hreach
      source_state state eq_refl eq_refl) as Hdecoded.
    rewrite section_right_project_lift_nvec,
      section_right_project_target in Hdecoded. exact Hdecoded.
Qed.

Theorem vass_section_union_reach_iff : forall d q
    (W1 W2 : VASSSection d q) state counters,
    VASSSectionReach (vass_section_union W1 W2) state counters <->
    VASSSectionReach W1 state counters \/ VASSSectionReach W2 state counters.
Proof.
  intros. split; [apply vass_section_union_sound|apply vass_section_union_complete].
Qed.

Fixpoint section_finite_union {d q} (sections : list (VASSSection d q)) :
    VASSSection d q :=
  match sections with
  | [] => empty_vass_section d q
  | section :: tail => vass_section_union section (section_finite_union tail)
  end.

Theorem section_finite_union_reach_iff : forall d q sections state counters,
    VASSSectionReach (@section_finite_union d q sections) state counters <->
    exists section, List.In section sections /\
      VASSSectionReach section state counters.
Proof.
  intros d q sections. induction sections as [|section tail IH];
    intros state counters; cbn.
  - split.
    + intro H. exfalso. eapply empty_vass_section_reach; exact H.
    + intros [selected [Hin _]]. contradiction.
  - rewrite vass_section_union_reach_iff, IH. split.
    + intros [H|[selected [Hin Hreach]]].
      * exists section. auto.
      * exists selected. auto.
    + intros [selected [[<-|Hin] Hreach]].
      * now left.
      * right. eauto.
Qed.

(** Unary closure of a section. *)
Definition unary_transition_of_rule {d q} (rule : SRule d q) :
    option (VASTransition d q) :=
  match input_states rule with
  | [source] =>
      Some {| VASTransitionSource := source;
              VASTransitionAction := rule_delta rule;
              VASTransitionTarget := output_state rule |}
  | _ => None
  end.

Fixpoint collect_some {A B} (f : A -> option B) (values : list A) : list B :=
  match values with
  | [] => []
  | value :: tail =>
      match f value with
      | Some result => result :: collect_some f tail
      | None => collect_some f tail
      end
  end.

Definition unary_vas {d q} (B : SBVAS d q) : VAS d q :=
  collect_some unary_transition_of_rule (stateful_rules B).

Lemma unary_vas_in_iff : forall d q (B : SBVAS d q) transition,
    List.In transition (unary_vas B) <->
    exists rule source,
      List.In rule (stateful_rules B) /\
      input_states rule = [source] /\
      transition =
        {| VASTransitionSource := source;
           VASTransitionAction := rule_delta rule;
           VASTransitionTarget := output_state rule |}.
Proof.
  intros d q B transition. unfold unary_vas.
  induction (stateful_rules B) as [|rule tail IH]; cbn.
  - split; [contradiction|intros [? [? [Hin _]]]; contradiction].
  - destruct (input_states rule) as [|source inputs] eqn:Hinputs.
    + exfalso. apply (input_nonempty rule). exact Hinputs.
    + destruct inputs as [|second rest].
      * unfold unary_transition_of_rule. rewrite Hinputs. cbn. rewrite IH. split.
        -- intros [<-|[selected [selected_source
             [Hin [Hstates ->]]]]].
           ++ exists rule, source. repeat split; auto.
           ++ exists selected, selected_source. repeat split; auto.
        -- intros [selected [selected_source
             [[<-|Hin] [Hstates ->]]]].
           ++ rewrite Hinputs in Hstates. inversion Hstates; subst.
              left. reflexivity.
           ++ right. exists selected, selected_source. repeat split; auto.
      * unfold unary_transition_of_rule. rewrite Hinputs. cbn. rewrite IH.
        split.
        -- intros [selected [selected_source [Hin [Hstates ->]]]].
           exists selected, selected_source. repeat split; auto.
        -- intros [selected [selected_source
             [[Heq|Hin] [Hstates ->]]]].
           ++ subst selected. rewrite Hinputs in Hstates. discriminate.
           ++ exists selected, selected_source. repeat split; auto.
Qed.

Definition unary_internal_state {d q} (W : VASSSection d q)
    (state : Fin.t (section_state_count W)) :
    Fin.t (section_state_count W + q) := Fin.L q state.

Definition unary_public_state {d q} (W : VASSSection d q)
    (state : Fin.t q) : Fin.t (section_state_count W + q) :=
  Fin.R (section_state_count W) state.

Definition unary_internal_transition {d q} (W : VASSSection d q)
    (transition : VASTransition
      (d + section_aux_dimension W) (section_state_count W)) :
    VASTransition (d + section_aux_dimension W)
      (section_state_count W + q) :=
  {| VASTransitionSource := unary_internal_state W
       (VASTransitionSource transition);
     VASTransitionAction := VASTransitionAction transition;
     VASTransitionTarget := unary_internal_state W
       (VASTransitionTarget transition) |}.

Definition unary_exit_transition {d q} (W : VASSSection d q)
    (state : Fin.t q) :
    VASTransition (d + section_aux_dimension W)
      (section_state_count W + q) :=
  {| VASTransitionSource := unary_internal_state W
       (section_accept_state W state);
     VASTransitionAction := zvec_zero (d + section_aux_dimension W);
     VASTransitionTarget := unary_public_state W state |}.

Definition unary_visible_action {d auxiliary} (action : ZVec d) :
    ZVec (d + auxiliary) :=
  Vector.append action (zvec_zero auxiliary).

Definition unary_public_transition {d q} (W : VASSSection d q)
    (transition : VASTransition d q) :
    VASTransition (d + section_aux_dimension W)
      (section_state_count W + q) :=
  {| VASTransitionSource := unary_public_state W
       (VASTransitionSource transition);
     VASTransitionAction := unary_visible_action
       (VASTransitionAction transition);
     VASTransitionTarget := unary_public_state W
       (VASTransitionTarget transition) |}.

Definition unary_closure_system {d q} (B : SBVAS d q)
    (W : VASSSection d q) :=
  List.map (unary_internal_transition W) (section_system W) ++
  List.map (unary_exit_transition W) (all_fin q) ++
  List.map (unary_public_transition W) (unary_vas B).

Definition unary_closure_initial {d q} (W : VASSSection d q)
    (config : Mell.VAS.StatefulVAS.SConfig
      (d + section_aux_dimension W) (section_state_count W)) :=
  (unary_internal_state W (fst config), snd config).

Definition compile_unary_closure {d q} (B : SBVAS d q)
    (W : VASSSection d q) : VASSSection d q :=
  {| section_aux_dimension := section_aux_dimension W;
     section_state_count := section_state_count W + q;
     section_system := unary_closure_system B W;
     section_initial_configs :=
       List.map (unary_closure_initial W) (section_initial_configs W);
     section_accept_state := unary_public_state W |}.

Definition UnaryClosure {d q} (B : SBVAS d q)
    (relation : Fin.t q -> NVec d -> Prop)
    (state : Fin.t q) (counters : NVec d) : Prop :=
  exists source_state source,
    relation source_state source /\
    DirectVASReach (unary_vas B)
      source_state source state counters.

Lemma unary_visible_step_action : forall d auxiliary
    (source target : NVec d),
    unary_visible_action (StepAction source target) =
    StepAction (Vector.append source (nvec_zero auxiliary))
      (Vector.append target (nvec_zero auxiliary)).
Proof.
  intros. unfold unary_visible_action.
  rewrite step_action_append, step_action_zero. reflexivity.
Qed.

Lemma unary_internal_transition_in : forall d q (B : SBVAS d q)
    (W : VASSSection d q) transition,
    List.In transition (section_system W) ->
    List.In (unary_internal_transition W transition)
      (unary_closure_system B W).
Proof.
  intros. unfold unary_closure_system. apply in_or_app. left.
  now apply List.in_map.
Qed.

Lemma unary_exit_transition_in : forall d q (B : SBVAS d q)
    (W : VASSSection d q) state,
    List.In (unary_exit_transition W state) (unary_closure_system B W).
Proof.
  intros. unfold unary_closure_system. apply in_or_app. right.
  apply in_or_app. left. apply List.in_map. apply all_fin_complete.
Qed.

Lemma unary_public_transition_in : forall d q (B : SBVAS d q)
    (W : VASSSection d q) transition,
    List.In transition (unary_vas B) ->
    List.In (unary_public_transition W transition)
      (unary_closure_system B W).
Proof.
  intros. unfold unary_closure_system. apply in_or_app. right.
  apply in_or_app. right. now apply List.in_map.
Qed.

Lemma unary_internal_direct_reach : forall d q (B : SBVAS d q)
    (W : VASSSection d q) source_state source target_state target,
    DirectVASReach (section_system W) source_state source target_state target ->
    DirectVASReach (unary_closure_system B W)
      (unary_internal_state W source_state) source
      (unary_internal_state W target_state) target.
Proof.
  intros d q B W source_state source target_state target Hreach.
  induction Hreach.
  - constructor.
  - eapply direct_vas_reach_step with
      (transition := unary_internal_transition W transition) (target := target).
    + now apply unary_internal_transition_in.
    + exact H0.
    + exact IHHreach.
Qed.

Lemma unary_public_direct_reach : forall d q (B : SBVAS d q)
    (W : VASSSection d q) source_state source target_state target,
    DirectVASReach (unary_vas B) source_state source target_state target ->
    DirectVASReach (unary_closure_system B W)
      (unary_public_state W source_state)
      (Vector.append source (nvec_zero (section_aux_dimension W)))
      (unary_public_state W target_state)
      (Vector.append target (nvec_zero (section_aux_dimension W))).
Proof.
  intros d q B W source_state source target_state target Hreach.
  induction Hreach.
  - constructor.
  - eapply direct_vas_reach_step with
      (transition := unary_public_transition W transition)
      (target := Vector.append target (nvec_zero (section_aux_dimension W))).
    + now apply unary_public_transition_in.
    + cbn. rewrite H0. apply unary_visible_step_action.
    + exact IHHreach.
Qed.

Theorem compile_unary_closure_complete : forall d q (B : SBVAS d q)
    (W : VASSSection d q) state counters,
    UnaryClosure B (VASSSectionReach W) state counters ->
    VASSSectionReach (compile_unary_closure B W) state counters.
Proof.
  intros d q B W state counters
    [source_state [source [Hsection Hunary]]].
  destruct Hsection as [initial_state [initial_counters [Hinitial Hreach]]].
  exists (unary_internal_state W initial_state), initial_counters. split.
  - apply List.in_map_iff. exists (initial_state, initial_counters).
    split; [reflexivity|exact Hinitial].
  - apply vas_reach_direct_iff in Hreach. apply vas_reach_direct_iff.
    change (DirectVASReach (unary_closure_system B W)
      (unary_internal_state W initial_state) initial_counters
      (unary_public_state W state)
      (Vector.append counters (nvec_zero (section_aux_dimension W)))).
    eapply direct_vas_reach_trans.
    + apply unary_internal_direct_reach. exact Hreach.
    + eapply direct_vas_reach_trans.
      * eapply direct_vas_reach_step with
          (transition := unary_exit_transition W source_state)
          (target := section_target_vector W source).
        -- apply unary_exit_transition_in.
        -- cbn. symmetry. apply step_action_refl.
        -- constructor.
      * unfold section_target_vector.
        apply unary_public_direct_reach. exact Hunary.
Qed.

Lemma unary_internal_public_distinct : forall d q (W : VASSSection d q)
    (internal : Fin.t (section_state_count W)) (public : Fin.t q),
    unary_internal_state W internal <> unary_public_state W public.
Proof.
  intros. unfold unary_internal_state, unary_public_state.
  apply fin_left_right_distinct.
Qed.

Lemma unary_internal_state_injective : forall d q (W : VASSSection d q)
    (left right : Fin.t (section_state_count W)),
    unary_internal_state W left = unary_internal_state W right -> left = right.
Proof.
  intros d q W left right Heq. unfold unary_internal_state in Heq.
  now apply Fin.L_inj in Heq.
Qed.

Lemma unary_public_state_injective : forall d q (W : VASSSection d q)
    (left right : Fin.t q),
    unary_public_state W left = unary_public_state W right -> left = right.
Proof.
  intros d q W left right Heq. unfold unary_public_state in Heq.
  now apply Fin.R_inj in Heq.
Qed.

Lemma unary_closure_transition_cases : forall d q (B : SBVAS d q)
    (W : VASSSection d q) transition,
    List.In transition (unary_closure_system B W) ->
    (exists original,
      List.In original (section_system W) /\
      transition = unary_internal_transition W original) \/
    (exists state, transition = unary_exit_transition W state) \/
    (exists original,
      List.In original (unary_vas B) /\
      transition = unary_public_transition W original).
Proof.
  intros d q B W transition Hin. unfold unary_closure_system in Hin.
  repeat rewrite in_app_iff in Hin.
  destruct Hin as [Hin|[Hin|Hin]].
  - left. apply List.in_map_iff in Hin as [original [<- Hin]]. eauto.
  - right; left. apply List.in_map_iff in Hin as [state [<- _]]. eauto.
  - right; right. apply List.in_map_iff in Hin as [original [<- Hin]]. eauto.
Qed.

Lemma step_action_zero_source : forall d (source target : NVec d),
    zvec_zero d = StepAction source target -> source = target.
Proof.
  intros d source target Heq.
  apply (proj1 (Vector.eq_nth_iff nat d source target)).
  intros index index' Hindex; subst index'.
  pose proof (f_equal (fun value => Vector.nth value index) Heq) as Hnth.
  unfold zvec_zero, StepAction, zvec_sub_run in Hnth.
  rewrite const_nth, (nth_map2 Z.sub _ _ index index index eq_refl eq_refl)
    in Hnth.
  unfold nvec_to_zvec in Hnth.
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl) in Hnth.
  assert (Hcast : Z.of_nat (Vector.nth source index) =
      Z.of_nat (Vector.nth target index)) by lia.
  now apply Nat2Z.inj in Hcast.
Qed.

Lemma unary_public_step_inv : forall d auxiliary (action : ZVec d)
    (source : NVec d) target,
    unary_visible_action action =
      StepAction (Vector.append source (nvec_zero auxiliary)) target ->
    exists target_visible,
      target = Vector.append target_visible (nvec_zero auxiliary) /\
      action = StepAction source target_visible.
Proof.
  intros d auxiliary action source target Haction.
  destruct (Vector.splitat d target) as [target_visible target_aux] eqn:Hsplit.
  apply VectorSpec.append_splitat in Hsplit. subst target.
  unfold unary_visible_action in Haction.
  rewrite step_action_append in Haction.
  apply Vector.append_inj in Haction as [Hvisible Haux].
  assert (Haux_zero : target_aux = nvec_zero auxiliary).
  { symmetry. now apply step_action_zero_source. }
  subst target_aux. exists target_visible. auto.
Qed.

Lemma unary_public_reach_inv : forall d q (B : SBVAS d q)
    (W : VASSSection d q) source_state source target_state target,
    DirectVASReach (unary_closure_system B W)
      (unary_public_state W source_state)
      (Vector.append source (nvec_zero (section_aux_dimension W)))
      (unary_public_state W target_state)
      (Vector.append target (nvec_zero (section_aux_dimension W))) ->
    DirectVASReach (unary_vas B) source_state source target_state target.
Proof.
  intros d q B W source_state source target_state target Hreach.
  remember (unary_public_state W source_state) as start_state eqn:Hstart.
  remember (Vector.append source (nvec_zero (section_aux_dimension W)))
    as start_counter eqn:Hcounter.
  remember (unary_public_state W target_state) as end_state eqn:Hend.
  remember (Vector.append target (nvec_zero (section_aux_dimension W)))
    as end_counter eqn:Hendcounter.
  revert source_state source target_state target
    Hstart Hcounter Hend Hendcounter.
  induction Hreach; intros source_state0 source0 target_state0 target0
      Hstart Hcounter Hend Hendcounter.
  - assert (Hstates : unary_public_state W source_state0 =
        unary_public_state W target_state0) by congruence.
    apply unary_public_state_injective in Hstates. subst target_state0.
    assert (Hcounters : Vector.append source0
        (nvec_zero (section_aux_dimension W)) =
        Vector.append target0 (nvec_zero (section_aux_dimension W))) by congruence.
    apply Vector.append_inj in Hcounters as [Hvisible _]. subst target0.
    constructor.
  - subst source.
    destruct (unary_closure_transition_cases d q B W transition H)
      as [[original [Hin ->]]|[[selected ->]|[original [Hin ->]]]];
      cbn in Hstart.
    + exfalso. eapply unary_internal_public_distinct. exact Hstart.
    + exfalso. eapply unary_internal_public_distinct. exact Hstart.
    + apply unary_public_state_injective in Hstart. subst source_state0.
      destruct (unary_public_step_inv d (section_aux_dimension W)
        (VASTransitionAction original) source0 target H0)
        as [next [-> Haction]].
      econstructor; eauto.
Qed.

Lemma unary_public_step_inv_backward : forall d auxiliary (action : ZVec d)
    source (target : NVec d),
    unary_visible_action action =
      StepAction source (Vector.append target (nvec_zero auxiliary)) ->
    exists source_visible,
      source = Vector.append source_visible (nvec_zero auxiliary) /\
      action = StepAction source_visible target.
Proof.
  intros d auxiliary action source target Haction.
  destruct (Vector.splitat d source) as [source_visible source_aux] eqn:Hsplit.
  apply VectorSpec.append_splitat in Hsplit. subst source.
  unfold unary_visible_action in Haction.
  rewrite step_action_append in Haction.
  apply Vector.append_inj in Haction as [Hvisible Haux].
  assert (Haux_zero : source_aux = nvec_zero auxiliary).
  { now apply step_action_zero_source in Haux. }
  subst source_aux. exists source_visible. auto.
Qed.

Lemma unary_public_reach_inv_backward : forall d q (B : SBVAS d q)
    (W : VASSSection d q) source_state source target_state target,
    DirectVASReach (unary_closure_system B W)
      (unary_public_state W source_state) source
      (unary_public_state W target_state)
      (Vector.append target (nvec_zero (section_aux_dimension W))) ->
    exists source_visible,
      source = Vector.append source_visible
        (nvec_zero (section_aux_dimension W)) /\
      DirectVASReach (unary_vas B)
        source_state source_visible target_state target.
Proof.
  intros d q B W source_state source target_state target Hreach.
  remember (unary_public_state W source_state) as start_state eqn:Hstart.
  remember (unary_public_state W target_state) as end_state eqn:Hend.
  remember (Vector.append target (nvec_zero (section_aux_dimension W)))
    as end_counter eqn:Hendcounter.
  revert source_state target_state target Hstart Hend Hendcounter.
  induction Hreach; intros source_state0 target_state0 target0
      Hstart Hend Hendcounter.
  - assert (Hstates : unary_public_state W source_state0 =
        unary_public_state W target_state0) by congruence.
    apply unary_public_state_injective in Hstates. subst target_state0.
    exists target0. split; [congruence|constructor].
  - destruct (unary_closure_transition_cases d q B W transition H)
      as [[original [Hin ->]]|[[selected ->]|[original [Hin ->]]]];
      cbn in Hstart.
    + exfalso. eapply unary_internal_public_distinct. exact Hstart.
    + exfalso. eapply unary_internal_public_distinct. exact Hstart.
    + apply unary_public_state_injective in Hstart. subst source_state0.
      destruct (IHHreach (VASTransitionTarget original) target_state0 target0
        eq_refl Hend Hendcounter) as [next [Hnext Htail]].
      subst target.
      destruct (unary_public_step_inv_backward d (section_aux_dimension W)
        (VASTransitionAction original) source next H0)
        as [source_visible [-> Haction]].
      exists source_visible. split; [reflexivity|]. econstructor; eauto.
Qed.

Lemma unary_internal_to_public_inv : forall d q (B : SBVAS d q)
    (W : VASSSection d q) internal_state source target_state target,
    DirectVASReach (unary_closure_system B W)
      (unary_internal_state W internal_state) source
      (unary_public_state W target_state)
      (Vector.append target (nvec_zero (section_aux_dimension W))) ->
    exists source_state source_visible,
      DirectVASReach (section_system W)
        internal_state source (section_accept_state W source_state)
        (Vector.append source_visible
          (nvec_zero (section_aux_dimension W))) /\
      DirectVASReach (unary_vas B)
        source_state source_visible target_state target.
Proof.
  intros d q B W internal_state source target_state target Hreach.
  remember (unary_internal_state W internal_state) as start_state eqn:Hstart.
  remember (unary_public_state W target_state) as end_state eqn:Hend.
  remember (Vector.append target (nvec_zero (section_aux_dimension W)))
    as end_counter eqn:Hendcounter.
  revert internal_state target_state target Hstart Hend Hendcounter.
  induction Hreach; intros internal_state0 target_state0 target0
      Hstart Hend Hendcounter.
  - exfalso. eapply unary_internal_public_distinct.
    transitivity state; [symmetry; exact Hstart|exact Hend].
  - destruct (unary_closure_transition_cases d q B W transition H)
      as [[original [Hin ->]]|[[selected ->]|[original [Hin ->]]]];
      cbn in Hstart.
    + apply unary_internal_state_injective in Hstart. subst internal_state0.
      destruct (IHHreach (VASTransitionTarget original) target_state0 target0
        eq_refl Hend Hendcounter)
        as [source_state [source_visible [Hinternal Hpublic]]].
      exists source_state, source_visible. split; [|exact Hpublic].
      econstructor; eauto.
    + apply unary_internal_state_injective in Hstart. subst internal_state0.
      assert (Hsame : source = target) by now apply step_action_zero_source.
      subst target.
      cbn in Hreach. rewrite Hend, Hendcounter in Hreach.
      destruct (unary_public_reach_inv_backward d q B W selected source
        target_state0 target0 Hreach)
        as [source_visible [Hsource Hpublic]].
      subst source. exists selected, source_visible. split; [constructor|exact Hpublic].
    + exfalso. eapply unary_internal_public_distinct. symmetry. exact Hstart.
Qed.

Theorem compile_unary_closure_sound : forall d q (B : SBVAS d q)
    (W : VASSSection d q) state counters,
    VASSSectionReach (compile_unary_closure B W) state counters ->
    UnaryClosure B (VASSSectionReach W) state counters.
Proof.
  intros d q B W state counters
    [initial_state [initial_counters [Hinitial Hreach]]].
  apply List.in_map_iff in Hinitial as [[original_state original_counters]
    [Hconfig Hinitial]].
  unfold unary_closure_initial in Hconfig. cbn in Hconfig.
  injection Hconfig as Hstate Hcounters. subst initial_state initial_counters.
  apply vas_reach_direct_iff in Hreach.
  change (DirectVASReach (unary_closure_system B W)
    (unary_internal_state W original_state) original_counters
    (unary_public_state W state)
    (Vector.append counters (nvec_zero (section_aux_dimension W)))) in Hreach.
  destruct (unary_internal_to_public_inv d q B W original_state
    original_counters state counters Hreach)
    as [source_state [source [Hinternal Hunary]]].
  exists source_state, source. split; [|exact Hunary].
  exists original_state, original_counters. split; [exact Hinitial|].
  apply vas_reach_direct_iff. exact Hinternal.
Qed.

Theorem compile_unary_closure_reach_iff : forall d q (B : SBVAS d q)
    (W : VASSSection d q) state counters,
    VASSSectionReach (compile_unary_closure B W) state counters <->
    UnaryClosure B (VASSSectionReach W) state counters.
Proof.
  intros. split; [apply compile_unary_closure_sound|
    apply compile_unary_closure_complete].
Qed.
