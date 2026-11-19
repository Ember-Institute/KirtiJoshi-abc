def toNNReal {e : ℝ≥0} (he : e ≠ 0) : ℤᵐ⁰ →*₀ ℝ≥0 where
  toFun := fun x ↦ if hx : x = 0 then 0 else e ^ (WithZero.unzero hx).toAdd
  map_zero' := rfl
  map_one' := by rw [dif_neg one_ne_zero, unzero_coe (x := 1), toAdd_one, zpow_zero]
  map_mul' x y := by
    by_cases hxy : x * y = 0
    · rcases mul_eq_zero.mp hxy with hx | hy

      · rw [dif_pos hxy, dif_pos hx, zero_mul]
      · rw [dif_pos hxy, dif_pos hy, mul_zero]
    · obtain ⟨hx, hy⟩ := mul_ne_zero_iff.mp hxy

      rw [dif_neg hxy, dif_neg hx, dif_neg hy, ← zpow_add' (Or.inl he), ← toAdd_mul]
      congr
      rw [← WithZero.coe_inj, WithZero.coe_mul, coe_unzero hx, coe_unzero hy, coe_unzero hxy]
