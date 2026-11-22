import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltComparison

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.GeometricTiltComparison

noncomputable section

variable {C C' : Type*} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable [NormedField C'] [IsUltrametricDist C'] [CompleteSpace C']
variable (e : C ≃+* C') (d : ℕ) (hd : 0 < d) (hnorm : ∀ x : C, ‖e x‖ ^ d = ‖x‖)
variable (p : ℕ) [Fact p.Prime]
variable [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable [Fact (0 < ‖(p : C')‖ ∧ ‖(p : C')‖ < 1)]

local notation "𝒪'" => LocalGeometricFontaine.integerRing C'
local notation "𝔭'" => Ideal.span {(p : 𝒪')}
local notation "𝒯" => GeometricTiltField.Source C p

/-- The pretilt comparison and the valuation-ring comparison commute with untilting. -/
theorem untilt_preTiltEquiv (x : 𝒯) :
    PreTilt.untilt (preTiltEquiv e d hd hnorm p x) =
      integerEquiv e d hd hnorm (PreTilt.untilt x) := by
  change Perfection.teichmuller p 𝔭' (preTiltEquiv e d hd hnorm p x) =
    integerEquiv e d hd hnorm (PreTilt.untilt x)
  apply Perfection.teichmuller_spec
  intro n
  let y := ((frobeniusEquiv 𝒯 p).symm^[n]) x
  have hcoeff : PreTilt.coeff 0 y = PreTilt.coeff n x := by
    simpa only [Nat.zero_add] using PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n x
  have hpow : PreTilt.untilt y ^ (p ^ n) = PreTilt.untilt x :=
    PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n
  refine ⟨integerEquiv e d hd hnorm (PreTilt.untilt y), ?_, ?_⟩
  · rw [← modPEquiv_mk, PreTilt.mk_untilt_eq_coeff_zero]
    exact (congrArg (modPEquiv e d hd hnorm p) hcoeff).trans
      (preTiltEquiv_coeff e d hd hnorm p x n).symm
  · rw [← map_pow, hpow, SModEq.idealQuotientMk]

end

end JoshiTeich.Act1Scene1.GeometricTiltComparison
