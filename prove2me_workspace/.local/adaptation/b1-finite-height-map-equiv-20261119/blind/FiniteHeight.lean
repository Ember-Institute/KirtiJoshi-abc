open NumberField

namespace AbcAdaptation.Tripod

noncomputable def finHeight {F : Type*} [Field F] [NumberField F] (y : F) : ℝ :=
  ∑ᶠ v : FinitePlace F, Real.posLog (v y)
