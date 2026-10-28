From Coq Require Import List.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Runs.
From Mell.Decision Require Import Invariant.
From Mell.Semilinear Require Import Closure Presentation.
From Mell.Separator Require Import Main WitnessUpdate.

Lemma singleton_complement_semilinear : forall d (target : NVec d),
  Semilinear (fun value => value <> target).
Proof.
  intros d target.
  apply semilinear_complement.
  exact (singleton_nset_semilinear d target).
Qed.

Theorem singleton_separator : forall d (system : IBVAS d) target,
  ~ Reach system target ->
  exists code : SemiCode d,
    InitialIncluded system (denote code) /\
    Closed system (denote code) /\
    ~ denote code target.
Proof.
  intros d system target Hunreachable.
  destruct (separator_S d system (fun value => value <> target)
    (singleton_complement_semilinear d target)) as [J [Hsemi [Hinitial
      [Hclosed Hsafe]]]].
  { intros value Hreach Heq. subst value. contradiction. }
  destruct Hsemi as [code Hcode].
  exists code. repeat split.
  - intros value Hin. apply (proj1 (Hcode value)), Hinitial, Hin.
  - intros action children value Haction Hchildren Happly.
    apply (proj1 (Hcode value)), Hclosed with (children := children)
      (action := action); try assumption.
    apply List.Forall_forall. intros child Hchild.
    apply (proj2 (Hcode child)).
    exact (proj1 (@List.Forall_forall (NVec d) (denote code) children)
      Hchildren child Hchild).
  - intro Htarget. apply (Hsafe target).
    apply (proj2 (Hcode target)). exact Htarget.
    reflexivity.
Qed.
