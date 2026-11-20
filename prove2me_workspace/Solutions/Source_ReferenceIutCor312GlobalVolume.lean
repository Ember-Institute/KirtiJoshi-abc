import Solutions.Source_ReferenceIutCor312ArchimedeanVolume
import Solutions.Source_ReferenceIutCor312VolumeAggregation
import Solutions.Source_ReferenceIutCor312FiniteThetaHullVolume

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open LocalConstruct

universe u

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG} {D : InitialThetaData AG TG}

private noncomputable abbrev concreteTheory (D : InitialThetaData AG TG) :
    LocalTheory.{u, u} D.Kt :=
  concreteLocalTheory (K := D.Kt)

local notation "𝓛" => concreteTheory D

private theorem packetVol_thetaHull_infinite_eq (TL : ThetaLocalData D 𝓛)
    (i : Fin ((D.ℓ - 1) / 2)) :
    let R := TL.rhsData
    R.vol.packetVol i .infinite ((R.thetaHull i).region .infinite) =
      ((i.1 + 2 : ℕ) : ℝ) * Real.log Real.pi := by
  have hcount := ThetaLocalData.packetVol_thetaHull_infinite (AG := AG) (TG := TG)
    (D := D) TL i
  exact hcount.trans (congrArg (fun k : ℕ => (k : ℝ) * Real.log Real.pi)
    (LocalTheory.card_labelType ((D.ℓ - 1) / 2) i))

/-- Sum the finite packet volumes and the infinite packet volume for one capsule. -/
theorem globalVol_thetaHull_eq (TL : ThetaLocalData D 𝓛) (QI : QPilotInputs D)
    (i : Fin ((D.ℓ - 1) / 2)) :
    hullGlobalVolume TL i = capsuleVolumeFormula (signedQPilotVolume TL QI) i :=
  globalVol_thetaHull_eq_of_packetVolumes (AG := AG) (TG := TG) (D := D) (LT := 𝓛) TL QI
    (packetVol_finite_thetaHull (D := D) TL QI) (packetVol_thetaHull_infinite_eq TL) i

/-- The capsule average gives the global right-hand side on the same concrete bundle. -/
theorem rhs_thetaHull_eq (TL : ThetaLocalData D 𝓛) (QI : QPilotInputs D) :
    let n : ℝ := (((D.ℓ - 1) / 2 : ℕ) : ℝ)
    (concreteVariantData D 𝓛 TL QI).rhsData.rhs =
      averageSlope n * signedQPilotVolume TL QI + averageArchVolume n :=
  rhs_thetaHull_eq_of_packetVolumes (AG := AG) (TG := TG) (D := D) (LT := 𝓛) TL QI
    (packetVol_finite_thetaHull (D := D) TL QI) (packetVol_thetaHull_infinite_eq TL)

/-- Corollary 3.12 on the concrete bundle is equivalent to the corresponding q-pilot bound. -/
theorem corollary312Variant_iff_absLogQ_bound (TL : ThetaLocalData D 𝓛) (QI : QPilotInputs D) :
    let n : ℝ := (((D.ℓ - 1) / 2 : ℕ) : ℝ)
    Corollary312Variant (concreteVariantData D 𝓛 TL QI) ↔
      (averageSlope n - 1) * (concreteVariantData D 𝓛 TL QI).qPilot.absLogQ ≤
        averageArchVolume n :=
  corollary312Variant_iff_absLogQ_bound_of_packetVolumes (AG := AG) (TG := TG) (D := D)
    (LT := 𝓛) TL QI (packetVol_finite_thetaHull (D := D) TL QI)
    (packetVol_thetaHull_infinite_eq TL)

end AbcAdaptation.Reference.Iut.ThetaLocalData
