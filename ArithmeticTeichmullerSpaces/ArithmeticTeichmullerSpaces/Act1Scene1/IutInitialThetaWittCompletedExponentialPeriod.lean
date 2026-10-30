import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittCompletedFrobeniusRecognition
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittIntegralExponentialPeriod

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-COMPLETED-EXPONENTIAL-PERIOD
source: Joshi II `se:ff-rings`, `pr:teichmuller-lift-A` and
`eq:tate-module-of-lubin-tate`, multiplicative-formal-group periods.
fidelity: any extension of the actual annular eigen exponential to the
original full common completion satisfies phi(x)=x^p. The overlap law
and faithfulness of an original radius prove this equation; it is not
an input. Completed Frobenius recognition then constructs an original
integral Teichmuller representative. The existing small scaling and
integral exponential comparison give an actual principal-unit period
and remove the p-power scaling. No bounded source lift is assumed.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the full common-ring extension is explicit.
Its existence for arbitrary annular exponentials remains open. This
does not classify all linear phi=p elements or their theta kernel.
Original carriers, norms and Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittCompletedExponentialPeriod

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusCompletion InitialThetaWittAllRadiusFrobenius
open InitialThetaWittEigenRadiusDynamics InitialThetaWittInverseRadiusOrbit
open InitialThetaWittRhoFrobeniusCompletion
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem equation_of_annular_lift (ρ : Radius) (z : Eigen D w)
    (hz : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      ‖evaluate D w s.val z.val‖ < s.val.val.toReal)
    (x : Carrier D w)
    (hx : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      InitialThetaWittAnnularExponential.evaluate D w ρ s
        (InitialThetaWittAnnularExponential.annularExp D w ρ z.val hz) = evaluate D w s.val x) :
    frobeniusEquiv D w x = x ^ Arithmetic.residueChar w.1 := by
  let s : InitialThetaWittAnnularExponential.AnnularRadius ρ :=
    ⟨orbit D w ρ 1, InitialThetaWittTeichmullerRecognition.base_le_inverse_radius D w ρ⟩
  have he : poweredRadius D w s.val = ρ := by
    change poweredRadius D w (orbit D w ρ (0 + 1)) = ρ
    rw [powered_orbit_succ, orbit_zero]
  have hs : ρ.val ≤ (poweredRadius D w s.val).val := by rw [he]
  have h := InitialThetaWittAnnularExponential.eigen_annular_frobenius D w ρ z hz s hs
  rw [hx s, hx ⟨poweredRadius D w s.val, hs⟩] at h
  apply InitialThetaWittRadiusFaithfulness.evaluate_injective D w (poweredRadius D w s.val)
  rw [evaluate_frobenius, map_pow]
  exact h

theorem exists_integral_teichmuller_of_annular_lift (ρ : Radius) (z : Eigen D w)
    (hz : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      ‖evaluate D w s.val z.val‖ < s.val.val.toReal)
    (x : Carrier D w)
    (hx : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      InitialThetaWittAnnularExponential.evaluate D w ρ s
        (InitialThetaWittAnnularExponential.annularExp D w ρ z.val hz) = evaluate D w s.val x) :
    ∃ a : InitialThetaTiltIntegers.Integers D w,
      InitialThetaWittAllRadiusExpansion.ainfMap D w
        (WittVector.teichmuller (Arithmetic.residueChar w.1) a) = x := by
  apply InitialThetaWittCompletedFrobeniusRecognition.exists_integral_teichmuller D w ρ x
    (equation_of_annular_lift D w ρ z hz x hx)
  change ‖evaluate D w ρ x‖ ≤ 1
  rw [← hx ⟨ρ, le_rfl⟩]
  exact InitialThetaWittAnnularExponential.norm_evaluate_annularExp_le_one D w ρ z.val hz ⟨ρ, le_rfl⟩

theorem exists_period_of_scaled_completed_annular_lift (ρ : Radius) (z : Eigen D w) (k : ℕ)
    (hz : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      ‖evaluate D w s.val
        (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val‖ < s.val.val.toReal)
    (hsmall : coordinateSeminorm D w ρ
      (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val ≤ ρ.val.toReal ^ 3 / 2)
    (x : Carrier D w)
    (hx : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      InitialThetaWittAnnularExponential.evaluate D w ρ s
        (InitialThetaWittAnnularExponential.annularExp D w ρ
          (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val hz) =
            evaluate D w s.val x) :
    ∃ u : InitialThetaWittPrincipalUnitDomain.Principal D w,
      InitialThetaWittPrincipalUnitPeriod.periodLog D w u = z.val := by
  obtain ⟨a, ha⟩ := exists_integral_teichmuller_of_annular_lift D w ρ _ hz x hx
  apply InitialThetaWittIntegralExponentialPeriod.exists_period_of_scaled_integral_annular_lift
    D w ρ z k hz hsmall (WittVector.teichmuller (Arithmetic.residueChar w.1) a)
  intro s
  rw [hx s, ← ha]
  rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittCompletedExponentialPeriod
