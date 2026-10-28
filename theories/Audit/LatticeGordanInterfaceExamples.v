From Coq Require Import List Vector ZArith.
From Mell.Geometry Require Import QConeCore RationalDefinability RationalHToV
  RationalConeAssembly LatticeGordanH LatticeGordanInterface.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Set Printing Implicit.

Check @FinitelyGeneratedGroup.
Check @RationalPolyhedralCone.
Print FinitelyGeneratedGroup.
Print RationalPolyhedralCone.
Check @finitely_generated_group_iff.
Check @zgroup_generated_is_finitely_generated_group.
Check @finitely_generated_group_ext.
Check @rational_polyhedral_cone_iff.
Check @qcone_generated_is_rational_polyhedral_cone.
Check @rational_polyhedral_cone_ext.
Check @rational_polyhedral_cone_qvec_ext.
Check @rational_hcone_is_polyhedral.
Check @rational_closed_cone_is_polyhedral.
Check lattice_gordan_contract.
Print lattice_gordan_contract.

Fail Check lattice_gordan.

Example group_interface_uses_integer_coefficients :
    FinitelyGeneratedGroup
      (@ZGroupGenerated 1
        [@Vector.cons Z 1%Z 0 (@Vector.nil Z)]).
Proof.
  apply (proj2 (finitely_generated_group_iff 1 _)).
  exists [@Vector.cons Z 1%Z 0 (@Vector.nil Z)].
  intro value. reflexivity.
Qed.

Example hmatrix_interface_is_v_represented : forall rows d
    (matrix : QMatrix rows d),
    RationalPolyhedralCone (@HConicalConstraints rows d matrix).
Proof. apply rational_hcone_is_polyhedral. Qed.

Example closed_definable_cone_interface : forall d (C : QSet d),
    QDefinable C -> IsCone C -> TopologicallyClosed C ->
    RationalPolyhedralCone C.
Proof. apply rational_closed_cone_is_polyhedral. Qed.

Print Assumptions finitely_generated_group_iff.
Print Assumptions zgroup_generated_is_finitely_generated_group.
Print Assumptions finitely_generated_group_ext.
Print Assumptions rational_polyhedral_cone_iff.
Print Assumptions qcone_generated_is_rational_polyhedral_cone.
Print Assumptions rational_polyhedral_cone_ext.
Print Assumptions rational_polyhedral_cone_qvec_ext.
Print Assumptions rational_hcone_is_polyhedral.
Print Assumptions rational_closed_cone_is_polyhedral.
