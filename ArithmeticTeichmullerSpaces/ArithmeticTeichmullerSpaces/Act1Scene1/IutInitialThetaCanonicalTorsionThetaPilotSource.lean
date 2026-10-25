import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionThetaPilotScaling

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open InitialThetaCanonicalGeometricFontaine

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-!
source-id: JT-SCENE1-CANONICAL-TORSION-THETA-PILOT-SOURCE
source: the actual torsion q-root untilt evaluation and finite theta pilot in
`IutInitialThetaTorsionThetaPilotScaling.lean`, from Joshi II
`pr:teichmuller-lift-A/B` and `thm:theta-pilot-object-appears`.
fidelity: packages the proved local pilot, its scaling law, period/log-shell
identity, and q-root power evaluation on one actual supported place.
boundary: this is a finite local pilot source. It does not construct a global
holomorphoid, cross-place marking, Frechet period carrier, or paper theta locus.
-/

namespace InitialThetaCanonicalTorsionThetaPilotSource

variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
variable (v : NumberField.FinitePlace ↥D.prime.torsionField)
variable (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.1.maximalIdeal.asIdeal)

abbrev Pilot := InitialThetaTorsionThetaPilotScaling.pilotData D w v hvw

structure Data : Type (u + 1) where
  thetaBase : InitialThetaTorsionThetaPilotScaling.PilotIndex D
  scaling : Theta.ThetaPilotScalingLaws (Pilot D w v hvw) thetaBase
  period_map : ∀ i, (Pilot D w v hvw).period i = (Pilot D w v hvw).liftedLog i
  theta_log_shell : ∀ i, (Pilot D w v hvw).liftedLog i =
      Real.log ((Pilot D w v hvw).norm i)
  qroot_value : ∀ i : InitialThetaTorsionThetaPilotScaling.PilotIndex D,
    (Pilot D w v hvw).value i =
      InitialThetaTorsionDeRhamPilot.rootImage D w v hvw ^ (i.down.val ^ 2)

noncomputable def canonical : Data D w v hvw where
  thetaBase := InitialThetaTorsionThetaPilotScaling.indexOne D
  scaling := InitialThetaTorsionThetaPilotScaling.pilotData_laws D w v hvw
  period_map := fun _ => rfl
  theta_log_shell := InitialThetaTorsionThetaPilotScaling.pilotData_log_shell D w v hvw
  qroot_value := InitialThetaTorsionThetaPilotScaling.pilotData_value_eq D w v hvw

theorem canonical_scaling :
    Theta.ThetaPilotScalingLaws (Pilot D w v hvw)
      (canonical D w v hvw).thetaBase :=
  (canonical D w v hvw).scaling

theorem canonical_log_shell
    (i : InitialThetaTorsionThetaPilotScaling.PilotIndex D) :
    (Pilot D w v hvw).liftedLog i =
      Real.log ((Pilot D w v hvw).norm i) :=
  (canonical D w v hvw).theta_log_shell i

end InitialThetaCanonicalTorsionThetaPilotSource

end
end JoshiTeich.Act1Scene1
