import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltComparison
import Solutions.Source_ReferenceIutCor312RootTowerPreTilt

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.LocalKummer.RootTower

open JoshiTeich.Prologue GeometricTiltComparison

noncomputable section

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
variable {C C' : Type*} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable [NormedField C'] [IsUltrametricDist C'] [CompleteSpace C']
variable {p : ℕ} [Fact p.Prime]
variable [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable [Fact (0 < ‖(p : C')‖ ∧ ‖(p : C')‖ < 1)]

/-- A coefficient-field equivalence with a norm power law carries the pretilt
of the original root tower to the same tower with the other embedding. -/
theorem preTiltEquiv_toGeometricPreTilt
    (e : C ≃+* C') (d : ℕ) (hd : 0 < d) (hnorm : ∀ x : C, ‖e x‖ ^ d = ‖x‖)
    {a : K} (R : RootTower (Ω := Ω) p a) (j : Ω →+* C) (j' : Ω →+* C')
    (hmap : ∀ z : Ω, e (j z) = j' z)
    (ha : ‖j (algebraMap K Ω a)‖ ≤ 1) (ha' : ‖j' (algebraMap K Ω a)‖ ≤ 1) :
    preTiltEquiv e d hd hnorm p (R.toGeometricPreTilt j ha) =
      R.toGeometricPreTilt j' ha' := by
  apply Perfection.ext
  intro n
  change PreTilt.coeff n (preTiltEquiv e d hd hnorm p (R.toGeometricPreTilt j ha)) =
    PreTilt.coeff n (R.toGeometricPreTilt j' ha')
  rw [preTiltEquiv_coeff]
  let q := Ideal.Quotient.mk (Ideal.span {(p : LocalGeometricFontaine.integerRing C)})
  let q' := Ideal.Quotient.mk (Ideal.span {(p : LocalGeometricFontaine.integerRing C')})
  change modPEquiv e d hd hnorm p (q (R.integralCoordinate j ha n)) =
    q' (R.integralCoordinate j' ha' n)
  rw [modPEquiv_mk]
  apply congrArg q'
  exact Subtype.ext (hmap (R.root n))

end

end JoshiTeich.Act1Scene1.LocalKummer.RootTower
