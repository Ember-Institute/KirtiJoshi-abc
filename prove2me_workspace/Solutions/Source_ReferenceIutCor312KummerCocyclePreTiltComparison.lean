import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltComparison
import Solutions.Source_ReferenceIutCor312KummerPreTiltGalois

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.LocalKummer.RootTower

open GeometricTiltComparison

noncomputable section

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
variable {C C' : Type*} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable [NormedField C'] [IsUltrametricDist C'] [CompleteSpace C']
variable {p : ℕ} [Fact p.Prime]
variable [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable [Fact (0 < ‖(p : C')‖ ∧ ‖(p : C')‖ < 1)]

/-- The pretilt comparison transports the cyclotomic coordinates of the
same Kummer cocycle value. -/
theorem preTiltEquiv_toPreTilt_mapKummerCocycle
    (e : C ≃+* C') (d : ℕ) (hd : 0 < d) (hnorm : ∀ x : C, ‖e x‖ ^ d = ‖x‖)
    {a : K} (R : RootTower (Ω := Ω) p a) (j : Ω →+* C) (j' : Ω →+* C')
    (hmap : ∀ z : Ω, e (j z) = j' z) (hne : a ≠ 0) (σ : Ω ≃ₐ[K] Ω) :
    preTiltEquiv e d hd hnorm p (CyclotomicTateTilt.toPreTilt C p (R.mapKummerCocycle j hne σ)) =
      CyclotomicTateTilt.toPreTilt C' p (R.mapKummerCocycle j' hne σ) := by
  let ε := R.mapKummerCocycle j hne σ
  let ε' := R.mapKummerCocycle j' hne σ
  apply Perfection.ext
  intro n
  change PreTilt.coeff n (preTiltEquiv e d hd hnorm p (CyclotomicTateTilt.toPreTilt C p ε)) =
    PreTilt.coeff n (CyclotomicTateTilt.toPreTilt C' p ε')
  rw [preTiltEquiv_coeff]
  let q := Ideal.Quotient.mk (Ideal.span {(p : LocalGeometricFontaine.integerRing C)})
  let q' := Ideal.Quotient.mk (Ideal.span {(p : LocalGeometricFontaine.integerRing C')})
  change modPEquiv e d hd hnorm p (q (CyclotomicTateTilt.coordinate C p ε n)) =
    q' (CyclotomicTateTilt.coordinate C' p ε' n)
  rw [modPEquiv_mk]
  apply congrArg q'
  apply Subtype.ext
  rw [integerEquiv_apply]
  change e (((R.mapKummerCocycle j hne σ).1 n : C)) =
    ((R.mapKummerCocycle j' hne σ).1 n : C')
  simp only [R.mapKummerCocycle_apply, map_div₀, hmap]

end

end JoshiTeich.Act1Scene1.LocalKummer.RootTower
