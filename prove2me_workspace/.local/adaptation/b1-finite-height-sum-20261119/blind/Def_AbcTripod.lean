open scoped IntermediateField Classical

namespace AbcAdaptation.Tripod

abbrev Qbar : Type := AlgebraicClosure ℚ

def Pt : Type := {z : Qbar // z ≠ 0 ∧ z ≠ 1}

noncomputable def residueChar {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) : ℕ :=
  ringChar (𝓞 K ⧸ v.maximalIdeal.asIdeal)
