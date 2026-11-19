class NumberField (K : Type*) [Field K] : Prop where
  [to_charZero : CharZero K]
  [to_finiteDimensional : FiniteDimensional ℚ K]

set_option backward.isDefEq.respectTransparency.types false in

def mapRingHom {K L : Type*} [Field K] [Field L] (f : K →+* L) : (𝓞 K) →+* (𝓞 L) where
  toFun k := ⟨f k.val, map_isIntegral_int f k.2⟩
  map_zero' := by ext; simp only [map_mk, map_zero]
  map_one' := by ext; simp only [map_mk, map_one]
  map_add' x y := by ext; simp only [map_mk, map_add]
  map_mul' x y := by ext; simp only [map_mk, map_mul]

@[simp]
theorem mapRingHom_apply {K L : Type*} [Field K] [Field L] (f : K →+* L) (x : 𝓞 K) :
    (mapRingHom f x : L) = f (x : K) := rfl

def mapRingEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) : (𝓞 K) ≃+* (𝓞 L) :=
  RingEquiv.ofRingHom (mapRingHom e) (mapRingHom e.symm)
    (RingHom.ext fun x => ext (EquivLike.right_inv e x.1))
      (RingHom.ext fun x => ext (EquivLike.left_inv e x.1))

@[simp]
theorem mapRingEquiv_apply {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (x : 𝓞 K) :
    (mapRingEquiv e x : L) = e (x : K) := rfl

@[simp]
theorem mapRingEquiv_symm_apply {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (x : 𝓞 L) :
    ((mapRingEquiv e).symm x : K) = e.symm (x : L) := rfl
