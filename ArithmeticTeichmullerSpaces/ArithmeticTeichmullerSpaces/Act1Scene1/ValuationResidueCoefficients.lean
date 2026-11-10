import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: the original coefficient field inside a valuation ring and its canonical residue map.
fidelity: forms the coefficient algebra on the actual residue field and sends
strictly small differences to zero. All maps use the original valuation ring.
boundary: no residue-field rationality or normalization comparison is supplied.
-/

namespace JoshiTeich.Act1Scene1.ValuationResidueCoefficients

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The residue field of the original valuation ring. -/
abbrev residueField (W : ValuationSubring K) := IsLocalRing.ResidueField W

/-- Restrict the original coefficient map to the valuation ring. -/
def coefficientMap (W : ValuationSubring K)
    (hk : ∀ c : k, algebraMap k K c ∈ W) : k →+* W where
  toFun c := ⟨algebraMap k K c, hk c⟩
  map_zero' := Subtype.ext (map_zero (algebraMap k K))
  map_one' := Subtype.ext (map_one (algebraMap k K))
  map_add' a b := Subtype.ext (map_add (algebraMap k K) a b)
  map_mul' a b := Subtype.ext (map_mul (algebraMap k K) a b)

/-- The original coefficient algebra on the valuation ring. -/
@[instance_reducible] def ringCoefficientAlgebra (W : ValuationSubring K)
    (hk : ∀ c : k, algebraMap k K c ∈ W) : Algebra k W :=
  (coefficientMap W hk).toAlgebra

/-- The canonical coefficient algebra on its residue field. -/
@[instance_reducible] def coefficientAlgebra (W : ValuationSubring K)
    (hk : ∀ c : k, algebraMap k K c ∈ W) : Algebra k (residueField W) := by
  letI := ringCoefficientAlgebra W hk
  exact inferInstance

/-- Taking the residue of an original constant is the residue coefficient map. -/
theorem residue_algebraMap (W : ValuationSubring K)
    (hk : ∀ c : k, algebraMap k K c ∈ W) (c : k) :
    letI := coefficientAlgebra W hk
    IsLocalRing.residue W ⟨algebraMap k K c, hk c⟩ =
      algebraMap k (residueField W) c := rfl

/-- A strictly small difference gives equality in the same residue field. -/
theorem residue_eq_of_sub_lt_one (W : ValuationSubring K) (a b : W)
    (h : W.valuation ((a : K) - (b : K)) < 1) :
    IsLocalRing.residue W a = IsLocalRing.residue W b := by
  apply sub_eq_zero.mp
  rw [← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact W.coe_mem_nonunits_iff.mp (W.mem_nonunits_iff.mpr h)

end
end JoshiTeich.Act1Scene1.ValuationResidueCoefficients
