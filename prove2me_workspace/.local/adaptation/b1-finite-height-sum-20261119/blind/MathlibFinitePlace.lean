def FinitePlace (K : Type*) [Field K] [NumberField K] :=
  {w : AbsoluteValue K ℝ // ∃ v : HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w}

instance : FunLike (FinitePlace K) K ℝ where
  coe w x := w.1 x
  coe_injective _ _ h := Subtype.ext (AbsoluteValue.ext <| congr_fun h)
