import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittBoundedFrobeniusIntegral
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittIntegralExponentialPeriod

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-BOUNDED-EXPONENTIAL-PERIOD
source: Joshi II `se:ff-rings`, `pr:teichmuller-lift-A` and
`eq:tate-module-of-lubin-tate`, multiplicative-formal-group periods.
fidelity: an actual bounded Witt representative of the constructed
annular eigen exponential obeys the source Frobenius-power equation.
Its proved unit norm bound removes both the p-denominator and the
nonintegral Teichmuller coefficient. Produces an original Ainf witness
and then an actual principal-unit period, removing p-power scaling.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; existence of an exact bounded source
representative remains explicit. Density alone does not supply it,
and full period representation is not asserted. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittBoundedExponentialPeriod

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open InitialThetaWittEigenRadiusDynamics InitialThetaWittInverseRadiusOrbit
open InitialThetaWittBoundedFrobeniusIntegral
open InitialThetaWittRhoFrobeniusCompletion
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem source_equation_of_annular_lift (ρ : Radius) (z : Eigen D w)
    (hz : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val z.val‖ < s.val.val.toReal)
    (x : InitialThetaBoundedWittLocalization.Ring D w)
    (hx : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      InitialThetaWittAnnularExponential.evaluate D w ρ s
        (InitialThetaWittAnnularExponential.annularExp D w ρ z.val hz) =
          InitialThetaWittRhoCompletion.inclusion D w s.val x) :
    InitialThetaBoundedWittLocalization.frobeniusEquiv D w x = x ^ Arithmetic.residueChar w.1 := by
  let s : InitialThetaWittAnnularExponential.AnnularRadius ρ :=
    ⟨orbit D w ρ 1, InitialThetaWittTeichmullerRecognition.base_le_inverse_radius D w ρ⟩
  have he : poweredRadius D w s.val = ρ := by
    change poweredRadius D w (orbit D w ρ (0 + 1)) = ρ
    rw [powered_orbit_succ, orbit_zero]
  have hs : ρ.val ≤ (poweredRadius D w s.val).val := by rw [he]
  have h := InitialThetaWittAnnularExponential.eigen_annular_frobenius D w ρ z hz s hs
  rw [hx s, hx ⟨poweredRadius D w s.val, hs⟩] at h
  exact source_equation_of_completed D w s.val x h

theorem exists_integral_of_annular_source_lift (ρ : Radius) (z : Eigen D w)
    (hz : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val z.val‖ < s.val.val.toReal)
    (x : InitialThetaBoundedWittLocalization.Ring D w)
    (hx : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      InitialThetaWittAnnularExponential.evaluate D w ρ s
        (InitialThetaWittAnnularExponential.annularExp D w ρ z.val hz) =
          InitialThetaWittRhoCompletion.inclusion D w s.val x) :
    ∃ a : InitialThetaTiltFontaine.Ainf D w, InitialThetaBoundedWittLocalization.inclusion D w a = x := by
  apply exists_integral_of_source_equation D w ρ x (source_equation_of_annular_lift D w ρ z hz x hx)
  rw [← InitialThetaWittRhoCompletion.inclusion_norm D w ρ x, ← hx ⟨ρ, le_rfl⟩]
  exact InitialThetaWittAnnularExponential.norm_evaluate_annularExp_le_one D w ρ z.val hz ⟨ρ, le_rfl⟩

theorem exists_period_of_scaled_bounded_annular_lift (ρ : Radius) (z : Eigen D w) (k : ℕ)
    (hz : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      ‖InitialThetaWittAllRadiusCompletion.evaluate D w s.val
        (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val‖ < s.val.val.toReal)
    (hsmall : InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ
      (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val ≤ ρ.val.toReal ^ 3 / 2)
    (x : InitialThetaBoundedWittLocalization.Ring D w)
    (hx : ∀ s : InitialThetaWittAnnularExponential.AnnularRadius ρ,
      InitialThetaWittAnnularExponential.evaluate D w ρ s
        (InitialThetaWittAnnularExponential.annularExp D w ρ
          (((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) • z).val hz) =
            InitialThetaWittRhoCompletion.inclusion D w s.val x) :
    ∃ u : InitialThetaWittPrincipalUnitDomain.Principal D w,
      InitialThetaWittPrincipalUnitPeriod.periodLog D w u = z.val := by
  obtain ⟨a, ha⟩ := exists_integral_of_annular_source_lift D w ρ _ hz x hx
  apply InitialThetaWittIntegralExponentialPeriod.exists_period_of_scaled_integral_annular_lift
    D w ρ z k hz hsmall a
  intro s
  rw [hx s, ← ha]
  rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittBoundedExponentialPeriod
