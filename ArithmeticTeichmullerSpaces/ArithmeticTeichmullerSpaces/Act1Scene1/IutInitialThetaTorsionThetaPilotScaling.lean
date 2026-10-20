import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTorsionDeRhamPilot

/-!
source-id: JT-SCENE1-INITIAL-THETA-TORSION-THETA-PILOT-SCALING
source: Joshi II `pr:teichmuller-lift-A/B` and
`thm:theta-pilot-object-appears` (940--1013), together with the actual
torsion-q-root untilt evaluation proved in this project.
fidelity: for a finite range of j, packages the actual j^2 evaluations of one
torsion q-root in the original de Rham untilt as ThetaPilotData and proves the
base index, nonzero values, positive norms and j^2 norm scaling. Period and
lifted-log fields are the actual real log of these evaluated norms. The range
is finite because the current carrier requires Fintype; it does not identify
different holomorphoids or build a global theta locus.
boundary: Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTorsionThetaPilotScaling

open JoshiTeich.Prologue InitialThetaCanonicalGeometricFontaine
open InitialThetaDeRhamCompletion
open InitialThetaTorsionDeRhamPilot
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
variable (v : NumberField.FinitePlace ↥D.prime.torsionField)
variable (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.1.maximalIdeal.asIdeal)

abbrev PilotIndex (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) : Type u :=
  ULift.{u, 0} (Fin (D.prime.ℓ + 1))

def indexOne : PilotIndex D := ⟨⟨1, by
  have h := D.prime.ℓ_prime.pos
  omega⟩⟩

def pilotData : ThetaPilotData (coefficientField D w) where
  index := PilotIndex D
  indexFintype := inferInstance
  value i := theta D w (pilot D w v hvw i.down.val)
  norm i := ‖theta D w (pilot D w v hvw i.down.val)‖
  scalingIndex i := i.down.val
  frobenius := id
  period i := Real.log ‖theta D w (pilot D w v hvw i.down.val)‖
  liftedLog i := Real.log ‖theta D w (pilot D w v hvw i.down.val)‖

theorem pilotData_value_eq (i : PilotIndex D) :
    (pilotData D w v hvw).value i = rootImage D w v hvw ^ (i.down.val ^ 2) :=
  theta_pilot D w v hvw i.down.val

theorem pilotData_norm_eq (i : PilotIndex D) :
    (pilotData D w v hvw).norm i =
      ‖rootImage D w v hvw‖ ^ (i.down.val ^ 2) := by
  change ‖theta D w (pilot D w v hvw i.down.val)‖ = _
  rw [theta_pilot, norm_pow]

theorem pilotData_laws :
    Theta.ThetaPilotScalingLaws (pilotData D w v hvw) (indexOne D) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · intro i
    change theta D w (pilot D w v hvw i.down.val) ≠ 0
    rw [theta_pilot]
    exact pow_ne_zero _ (rootImage_ne_zero D w v hvw)
  · intro i
    change 0 < ‖theta D w (pilot D w v hvw i.down.val)‖
    rw [theta_pilot, norm_pow]
    exact pow_pos (norm_pos_iff.mpr (rootImage_ne_zero D w v hvw)) _
  · intro i
    change ‖theta D w (pilot D w v hvw i.down.val)‖ =
      ‖theta D w (pilot D w v hvw (indexOne D).down.val)‖ ^
        (i.down.val * i.down.val)
    rw [theta_pilot, theta_pilot]
    rw [norm_pow, norm_pow]
    simp only [indexOne]
    norm_num [pow_two]

theorem pilotData_log_shell (i : PilotIndex D) :
    (pilotData D w v hvw).liftedLog i =
      Real.log ((pilotData D w v hvw).norm i) := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaTorsionThetaPilotScaling
