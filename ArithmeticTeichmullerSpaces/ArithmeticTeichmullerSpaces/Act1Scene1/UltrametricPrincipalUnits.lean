import Mathlib.Analysis.Normed.Field.Ultra

/-!
source-id: JT-SCENE1-ULTRAMETRIC-PRINCIPAL-UNITS
source: Joshi II `se:ff-rings` and the multiplicative formal group
1+m_F in the period description following `pr:teichmuller-lift-A`.
fidelity: constructs the norm-defined principal-unit subgroup of any
ultrametric normed field, without a characteristic-zero or discrete
valuation assumption. Its elements have norm one.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; tilt and period consumers use their actual
field and its original norm. No logarithm law is assumed.
-/

namespace JoshiTeich.Act1Scene1.UltrametricPrincipalUnits

noncomputable section
variable (F : Type*) [NormedField F] [IsUltrametricDist F]

theorem norm_eq_one {x : F} (hx : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have hlt : ‖x + (-1)‖ < max ‖x‖ ‖(-1 : F)‖ := by
    rw [← sub_eq_add_neg, norm_neg, norm_one]
    exact hx.trans_le (le_max_right _ _)
  simpa only [norm_neg, norm_one] using IsUltrametricDist.norm_eq_of_add_norm_lt_max hlt

theorem mul_near_one {x y : F} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) :
    ‖x * y - 1‖ < 1 := by
  have he : x * y - 1 = (x - 1) * y + (y - 1) := by ring
  rw [he]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans_lt
  rw [norm_mul, norm_eq_one F hy, mul_one]
  exact max_lt hx hy

theorem inv_near_one (x : Fˣ) (hx : ‖(x : F) - 1‖ < 1) :
    ‖((x⁻¹ : Fˣ) : F) - 1‖ < 1 := by
  rw [Units.val_inv_eq_inv_val]
  calc
    ‖(x : F)⁻¹ - 1‖ = ‖(1 - (x : F)) * (x : F)⁻¹‖ := by
      rw [sub_mul, one_mul, mul_inv_cancel₀ x.ne_zero]
    _ = ‖(x : F) - 1‖ := by
      rw [norm_mul, norm_inv, norm_eq_one F hx, inv_one, mul_one, norm_sub_rev]
    _ < 1 := hx

def subgroup : Subgroup Fˣ where
  carrier := {x | ‖(x : F) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' := fun hx hy => mul_near_one F hx hy
  inv_mem' := fun hx => inv_near_one F _ hx

theorem norm_coe (x : subgroup F) : ‖((x : Fˣ) : F)‖ = 1 := norm_eq_one F x.property

end
end JoshiTeich.Act1Scene1.UltrametricPrincipalUnits
