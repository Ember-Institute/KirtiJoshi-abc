def FinitePlace (K : Type*) [Field K] [NumberField K] :=
  {w : AbsoluteValue K ℝ // ∃ v : HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w}

noncomputable def FinitePlace.mk [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : FinitePlace K :=
  ⟨place (embedding v), ⟨v, rfl⟩⟩

namespace FinitePlace

variable [NumberField K]

instance : FunLike (FinitePlace K) K ℝ where
  coe w x := w.1 x
  coe_injective _ _ h := Subtype.ext (AbsoluteValue.ext <| congr_fun h)

instance : MonoidWithZeroHomClass (FinitePlace K) K ℝ where
  map_mul w := w.1.map_mul
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero

noncomputable def maximalIdeal (w : FinitePlace K) : HeightOneSpectrum (𝓞 K) := w.2.choose

@[simp]
theorem mk_maximalIdeal (w : FinitePlace K) : mk (maximalIdeal w) = w := Subtype.ext w.2.choose_spec

@[simp]
theorem norm_embedding_eq (w : FinitePlace K) (x : K) :
    ‖embedding (maximalIdeal w) x‖ = w x := by
  conv_rhs => rw [← mk_maximalIdeal w, mk_apply]

theorem maximalIdeal_mk (v : HeightOneSpectrum (𝓞 K)) : maximalIdeal (mk v) = v := by
  rw [← mk_eq_iff, mk_maximalIdeal]

@[simps apply]
noncomputable def equivHeightOneSpectrum :
    FinitePlace K ≃ HeightOneSpectrum (𝓞 K) where
  toFun := maximalIdeal
  invFun := mk
  left_inv := mk_maximalIdeal
  right_inv := maximalIdeal_mk
