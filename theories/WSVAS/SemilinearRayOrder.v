From Coq Require Import List Vector Lia.
From KruskalTrees Require Import idx.
From KruskalAfProp Require Import af.af af.af_tools.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Presentation LinearEquations Closure.
From Mell.Order Require Import PeriodicOrder.
From Mell.VAS Require Import JancarOrder.
From Mell.WSVAS Require Import WitnessAlphabet.

Import ListNotations idx_notations.

Definition RayLe {d} (set : NVec d -> Prop) (left right : NVec d) : Prop :=
  exists direction,
    right = nvec_add left direction /\
    forall coefficient,
      set (nvec_add left (nvec_scale coefficient direction)).

Section ComponentRay.
Context {d : nat} (code : SemiCode d).

Definition component_witness_value
    (witness : ComponentWitness code) : NVec d :=
  match witness with
  | existT index coefficients => component_value code index coefficients
  end.

Lemma component_contribution_zero : forall index,
  component_contribution code index
    (Vector.const 0 (length (snd (component_at code index)))) = nvec_zero d.
Proof.
  intro index.
  pose proof (component_contribution_spec code index
    (Vector.const 0 (length (snd (component_at code index))))) as Hspec.
  rewrite Vector.to_list_const, weighted_sum_zero_coefficients in Hspec.
  now inversion Hspec.
Qed.

Lemma component_contribution_scale : forall index coefficient values,
  component_contribution code index (nvec_scale coefficient values) =
  nvec_scale coefficient (component_contribution code index values).
Proof.
  intros index coefficient. induction coefficient as [|coefficient IH]; intro values.
  - rewrite !nvec_scale_zero. apply component_contribution_zero.
  - rewrite !nvec_scale_succ, component_contribution_add, IH. reflexivity.
Qed.

Lemma component_witness_denotes : forall witness,
  denote code (component_witness_value witness).
Proof.
  intros [index coefficients]. exists (component_at code index). split.
  - apply component_at_in.
  - apply component_value_denotes.
Qed.

Lemma denote_has_component_witness : forall value,
  denote code value ->
  exists witness, component_witness_value witness = value.
Proof.
  intros value [component [Hin Hlinear]].
  destruct (vas_nth_idx_occurrence _ code component Hin) as [index Hindex].
  destruct (linear_denote_has_coefficients component value Hlinear)
    as [coefficients Hvalue].
  subst component. exists (@existT _ (ComponentCoefficients code) index coefficients).
  unfold component_witness_value, component_value, component_contribution.
  unfold component_at. symmetry. exact Hvalue.
Qed.

Lemma component_witness_le_ray : forall left right,
  component_witness_le code left right ->
  RayLe (denote code)
    (component_witness_value left) (component_witness_value right).
Proof.
  intros [left_index left_coefficients] [right_index right_coefficients]
    [Heq Hle]. destruct Heq.
  set (difference := nvec_sub_local right_coefficients left_coefficients).
  assert (Hright : right_coefficients =
      nvec_add left_coefficients difference).
  { unfold difference. apply nvec_sub_exact_local. exact Hle. }
  set (direction := component_contribution code left_index difference).
  exists direction. split.
  - unfold component_witness_value, component_value.
    rewrite Hright, component_contribution_add.
    unfold direction. symmetry. apply nvec_add_assoc_local.
  - intro coefficient.
    exists (component_at code left_index). split; [apply component_at_in|].
    replace (nvec_add (component_witness_value
        (existT (ComponentCoefficients code) left_index left_coefficients))
        (nvec_scale coefficient direction)) with
      (component_value code left_index
        (nvec_add left_coefficients (nvec_scale coefficient difference))).
    + apply component_value_denotes.
    + unfold component_witness_value, component_value, direction.
      rewrite component_contribution_add, component_contribution_scale.
      symmetry. apply nvec_add_assoc_local.
Qed.

Theorem semicode_ray_almost_full :
  @afs (NVec d) (denote code) (RayLe (denote code)).
Proof.
  apply af_sub_rel_afs.
  eapply af_rel_morph with
    (X := ComponentWitness code)
    (f := fun witness value =>
      component_witness_value witness = proj1_sig value)
    (R := component_witness_le code).
  - intros [value Hvalue]. cbn.
    destruct (denote_has_component_witness value Hvalue) as [witness Heq].
    exists witness. exact Heq.
  - intros left right [left_value Hleft] [right_value Hright]
      Hleft_eq Hright_eq Hle. cbn in *.
    subst left_value right_value. now apply component_witness_le_ray.
  - apply component_witness_le_wqo.
Qed.

End ComponentRay.

Theorem semilinear_ray_almost_full : forall d (set : NSet d),
  Semilinear set -> @afs (NVec d) set (RayLe set).
Proof.
  intros d set [code Hcode].
  eapply afs_mono with
    (P := denote code) (R := RayLe (denote code)).
  - intro value. apply Hcode.
  - intros left right Hleft Hright [direction [Heq Hray]].
    exists direction. split; [exact Heq|].
    intro coefficient. apply (proj2 (Hcode _)), Hray.
  - apply semicode_ray_almost_full.
Qed.

Theorem semilinear_complement_ray_almost_full : forall d (set : NSet d),
  Semilinear set ->
  @afs (NVec d) (fun value => ~ set value)
    (RayLe (fun value => ~ set value)).
Proof.
  intros d set Hset. apply semilinear_ray_almost_full.
  now apply semilinear_complement.
Qed.
