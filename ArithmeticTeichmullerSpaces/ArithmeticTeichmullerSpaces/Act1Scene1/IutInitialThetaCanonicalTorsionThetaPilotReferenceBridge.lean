import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalTorsionThetaPilotSource

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open InitialThetaCanonicalGeometricFontaine

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-CANONICAL-TORSION-THETA-PILOT-REFERENCE-BRIDGE
source: actual torsion theta pilot evaluation and Tate norm scaling from
`IutInitialThetaTorsionDeRhamPilot.lean` and Joshi II
`thm:theta-pilot-object-appears`.
fidelity: identifies the local pilot period with the actual Tate-parameter
log norm using the proved `j²/(2ℓ)` scaling.
boundary: this is a local actual normalization bridge. It does not identify
the period with a paper Frechet period or global theta-volume normalization.
-/

namespace InitialThetaCanonicalTorsionThetaPilotSource

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
variable (v : NumberField.FinitePlace ↥D.prime.torsionField)
variable (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.1.maximalIdeal.asIdeal)

theorem canonical_period_eq_tate_log
    (i : InitialThetaTorsionThetaPilotScaling.PilotIndex D) :
    (Pilot D w v hvw).period i =
      ((i.down.val ^ 2 : ℕ) : ℝ) /
          ((2 * D.prime.ℓ : ℕ) : ℝ) *
        Real.log ((iutInitialThetaTateParameterData D).norm w.1) := by
  simpa [Pilot, InitialThetaTorsionThetaPilotScaling.pilotData] using
    InitialThetaTorsionDeRhamPilot.evaluation_log_eq_tate D w v hvw i.down.val

end InitialThetaCanonicalTorsionThetaPilotSource

end
end JoshiTeich.Act1Scene1
