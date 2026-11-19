noncomputable def residueChar (w : FinitePlace k) : ℕ :=
  ringChar (𝓞 k ⧸ w.maximalIdeal.asIdeal)
