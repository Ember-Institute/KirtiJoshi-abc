import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.SimpleRing.Basic

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: elementary coefficient-field algebra and Mathlib's algebra equivalence API.
fidelity: constructs an equivalence from the coefficient map itself, without a new hypothesis.
boundary: the actual consumer must prove surjectivity for its original residue field.
-/

namespace JoshiTeich.Act1Scene1.NormalizationResidueConstants

noncomputable section

/-- A surjective coefficient map is an algebra equivalence of fields. -/
def coefficientEquivOfSurjective
    (k L : Type*) [Field k] [Field L] [Algebra k L]
    (h : Function.Surjective (algebraMap k L)) : k ≃ₐ[k] L :=
  AlgEquiv.ofBijective (Algebra.ofId k L) ⟨(algebraMap k L).injective, h⟩

/-- A coefficient algebra equivalence gives coefficient dimension one. -/
theorem coefficient_finrank_eq_one
    (k L : Type*) [Field k] [Field L] [Algebra k L]
    (e : k ≃ₐ[k] L) : Module.finrank k L = 1 :=
  e.toLinearEquiv.finrank_eq.symm.trans
    (CommSemiring.finrank_self k)

end
end JoshiTeich.Act1Scene1.NormalizationResidueConstants
