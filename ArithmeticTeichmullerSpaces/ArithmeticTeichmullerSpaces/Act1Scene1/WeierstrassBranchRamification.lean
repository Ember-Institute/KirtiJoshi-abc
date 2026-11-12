import ArithmeticTeichmullerSpaces.Act1Scene1.WeierstrassBranchLocus
import ArithmeticTeichmullerSpaces.Act1Scene1.DedekindEtale

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's ramification-one criterion and the proved Weierstrass etale locus.
fidelity: the actual x-projection has index one at a prime exactly when the
two-torsion polynomial is absent from the contracted prime. Finiteness,
flatness and residue separability are proved from the original coordinate ring.
boundary: Scene1/Derived. Orbicurve realization and the full producer remain open.
-/

namespace JoshiTeich.Act1Scene1.WeierstrassBranchLocus

open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section
variable {k : Type*} [Field k] [CharZero k] (W : WeierstrassCurve.Affine k)

theorem ramificationIdx_one_iff (q : Ideal W.CoordinateRing) [q.IsPrime] :
    q.ramificationIdx k[X] = 1 ↔ branchElement W ∉ q := by
  have : Module.Finite k[X] W.CoordinateRing :=
    Module.Finite.of_basis (Affine.CoordinateRing.basis W)
  have : Algebra.FinitePresentation k[X] W.CoordinateRing :=
    AdjoinRoot.finitePresentation W.polynomial
  have : CharZero (q.under k[X]).ResidueField := DedekindEtale.residueField_charZero (K := k) _
  have : PerfectField (q.under k[X]).ResidueField := inferInstance
  rw [Ideal.ramificationIdx_eq_one_iff]
  constructor
  · intro h
    have := h
    exact (isEtaleAt_iff W q).mp (Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q)
  · intro h
    have := (isEtaleAt_iff W q).mpr h
    infer_instance

theorem ramificationIdx_one_iff_twoTorsion_not_mem (q : Ideal W.CoordinateRing) [q.IsPrime] :
    q.ramificationIdx k[X] = 1 ↔ W.twoTorsionPolynomial.toPoly ∉ q.under k[X] := by
  rw [ramificationIdx_one_iff, branchElement_mem_iff]

end
end JoshiTeich.Act1Scene1.WeierstrassBranchLocus
