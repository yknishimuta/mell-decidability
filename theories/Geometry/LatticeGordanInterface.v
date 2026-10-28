From Coq Require Import List Vector.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge QConeCore
  RationalDefinability RationalHToV RationalConeAssembly LatticeGordanH.
From Mell.Order Require Import PeriodicOrder.

Definition FinitelyGeneratedGroup {d} (group : ZSet d) : Prop :=
  exists generators : list (ZVec d),
    SameSet group (ZGroupGenerated generators).

Definition RationalPolyhedralCone {d} (cone : QSet d) : Prop :=
  exists generators : list (QVec d),
    SameSet cone (qcone_generated generators).

Lemma finitely_generated_group_iff : forall d (group : ZSet d),
    FinitelyGeneratedGroup group <->
    exists generators : list (ZVec d),
      forall value, group value <-> ZGroupGenerated generators value.
Proof. intros; reflexivity. Qed.

Lemma rational_polyhedral_cone_iff : forall d (cone : QSet d),
    RationalPolyhedralCone cone <->
    exists generators : list (QVec d),
      forall value, cone value <-> qcone_generated generators value.
Proof. intros; reflexivity. Qed.

Lemma zgroup_generated_is_finitely_generated_group : forall d
    (generators : list (ZVec d)),
    FinitelyGeneratedGroup (@ZGroupGenerated d generators).
Proof.
  intros d generators. exists generators. intro value. reflexivity.
Qed.

Lemma qcone_generated_is_rational_polyhedral_cone : forall d
    (generators : list (QVec d)),
    RationalPolyhedralCone (@qcone_generated d generators).
Proof.
  intros d generators. exists generators. intro value. reflexivity.
Qed.

Lemma finitely_generated_group_ext : forall d (left right : ZSet d),
    SameSet left right ->
    (FinitelyGeneratedGroup left <-> FinitelyGeneratedGroup right).
Proof.
  intros d left right Heq. split.
  - intros [generators Hgenerated]. exists generators. intro value.
    rewrite <- (Heq value). apply Hgenerated.
  - intros [generators Hgenerated]. exists generators. intro value.
    rewrite (Heq value). apply Hgenerated.
Qed.

Lemma rational_polyhedral_cone_ext : forall d (left right : QSet d),
    SameSet left right ->
    (RationalPolyhedralCone left <-> RationalPolyhedralCone right).
Proof.
  intros d left right Heq. split.
  - intros [generators Hgenerated]. exists generators. intro value.
    rewrite <- (Heq value). apply Hgenerated.
  - intros [generators Hgenerated]. exists generators. intro value.
    rewrite (Heq value). apply Hgenerated.
Qed.

Lemma rational_polyhedral_cone_qvec_ext : forall d (cone : QSet d),
    RationalPolyhedralCone cone -> forall left right,
    QVecEq left right -> (cone left <-> cone right).
Proof.
  intros d cone [generators Hgenerated] left right Heq.
  rewrite (Hgenerated left), (Hgenerated right).
  apply qcone_generated_qvec_ext. exact Heq.
Qed.

Theorem rational_hcone_is_polyhedral : forall rows d
    (matrix : QMatrix rows d),
    RationalPolyhedralCone (@HConicalConstraints rows d matrix).
Proof.
  intros rows d matrix.
  destruct (rational_hcone_finitely_generated rows d matrix) as
    [generators Hgenerated].
  exists generators. exact Hgenerated.
Qed.

Theorem rational_closed_cone_is_polyhedral : forall d (cone : QSet d),
    QDefinable cone -> IsCone cone -> TopologicallyClosed cone ->
    RationalPolyhedralCone cone.
Proof.
  intros d cone Hdefinable Hcone Hclosed.
  destruct (rational_closed_cone_finitely_generated d cone
    Hdefinable Hcone Hclosed) as [generators Hgenerated].
  exists generators. exact Hgenerated.
Qed.

Definition lattice_gordan_contract : Prop :=
  forall d (group : ZSet d) (cone : QSet d),
    FinitelyGeneratedGroup group ->
    RationalPolyhedralCone cone ->
    FinitelyGeneratedPeriodic
      (fun value => group value /\ cone (zvec_to_qvec value)).
