import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrechetComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittAllRadiusComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrechetTopology

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-FRECHET-COMPARISON
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, completion
of the bounded Witt period subring for the entire family of rho norms.
fidelity: compares the original actual Hausdorff completion with the
independent standard Hausdorff completion. Both are constructed from their
original bounded rings and all-radius uniformities. The map is a continuous
ring equivalence and a uniform equivalence, and its coordinates preserve
the proved local-degree norm power law. The original bounded inclusion is
identified by the already proved native standard diagonal identity.
The standard completion is independently metrizable, and its rational
radius maps detect convergence of the original actual completion.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
boundary: multiplicative norm equality, scalar/Frobenius/period transport
and paper B/general E/H1e/BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittFrechetComparison

open JoshiTeich.Prologue
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeFrechetComparison : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev ActualCompleted := InitialThetaWittFrechetComparison.Completed D w
abbrev StandardCarrier := PadicWittAllRadiusCompletion.Carrier (Arithmetic.residueChar w.1)
abbrev StandardCompleted := PadicWittFrechetComparison.Completed (Arithmetic.residueChar w.1)

def carrierRingEquiv : ActualCompleted D w ≃+* StandardCarrier D w :=
  (InitialThetaWittFrechetComparison.ringEquiv D w).trans
    (InitialThetaPadicWittAllRadiusComparison.ringEquiv D w)

theorem carrierRingEquiv_continuous : Continuous (carrierRingEquiv D w) :=
  (InitialThetaPadicWittAllRadiusComparison.ringEquiv_continuous D w).comp
    (InitialThetaWittFrechetComparison.ringEquiv_continuous D w)

theorem carrierRingEquiv_symm_continuous : Continuous (carrierRingEquiv D w).symm :=
  (InitialThetaWittFrechetComparison.ringEquiv_symm_continuous D w).comp
    (InitialThetaPadicWittAllRadiusComparison.ringEquiv_symm_continuous D w)

def ringEquiv : ActualCompleted D w ≃+* StandardCompleted D w :=
  (carrierRingEquiv D w).trans
    (PadicWittFrechetComparison.ringEquiv (Arithmetic.residueChar w.1)).symm

theorem ringEquiv_continuous : Continuous (ringEquiv D w) :=
  (PadicWittFrechetComparison.ringEquiv_symm_continuous (Arithmetic.residueChar w.1)).comp
    (carrierRingEquiv_continuous D w)

theorem ringEquiv_symm_continuous : Continuous (ringEquiv D w).symm :=
  (carrierRingEquiv_symm_continuous D w).comp
    (PadicWittFrechetComparison.ringEquiv_continuous (Arithmetic.residueChar w.1))

theorem ringEquiv_uniformContinuous : UniformContinuous (ringEquiv D w) :=
  uniformContinuous_addMonoidHom_of_continuous
    (f := (ringEquiv D w).toAddMonoidHom) (ringEquiv_continuous D w)

theorem ringEquiv_symm_uniformContinuous : UniformContinuous (ringEquiv D w).symm :=
  uniformContinuous_addMonoidHom_of_continuous
    (f := (ringEquiv D w).symm.toAddMonoidHom) (ringEquiv_symm_continuous D w)

def uniformEquiv : ActualCompleted D w ≃ᵤ StandardCompleted D w where
  toEquiv := (ringEquiv D w).toEquiv
  uniformContinuous_toFun := ringEquiv_uniformContinuous D w
  uniformContinuous_invFun := ringEquiv_symm_uniformContinuous D w

def homeomorph : ActualCompleted D w ≃ₜ StandardCompleted D w :=
  (uniformEquiv D w).toHomeomorph

theorem standardCompleted_metrizable :
    TopologicalSpace.MetrizableSpace (StandardCompleted D w) := inferInstance

theorem ringEquiv_toCarrier (x : ActualCompleted D w) :
    PadicWittFrechetComparison.ringEquiv (Arithmetic.residueChar w.1)
        (ringEquiv D w x) = carrierRingEquiv D w x :=
  (PadicWittFrechetComparison.ringEquiv (Arithmetic.residueChar w.1)).apply_symm_apply _

theorem carrierRingEquiv_originalInclusion_val
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    (carrierRingEquiv D w
        (InitialThetaWittFrechetComparison.originalInclusion D w x)).val =
      PadicWittAllRadiusCompletion.diagonalFun (Arithmetic.residueChar w.1)
        (InitialThetaPadicBoundedWittComparison.ringFun D w x) := by
  change (InitialThetaPadicWittAllRadiusComparison.ringEquiv D w
    (InitialThetaWittFrechetComparison.ringEquiv D w
      (InitialThetaWittFrechetComparison.originalInclusion D w x))).val = _
  rw [InitialThetaWittFrechetComparison.ringEquiv_originalInclusion]
  exact InitialThetaPadicWittAllRadiusComparison.ringEquiv_inclusion_val D w x

theorem ringEquiv_originalInclusion_val
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    (PadicWittFrechetComparison.ringEquiv (Arithmetic.residueChar w.1)
      (ringEquiv D w (InitialThetaWittFrechetComparison.originalInclusion D w x))).val =
      PadicWittAllRadiusCompletion.diagonalFun (Arithmetic.residueChar w.1)
        (InitialThetaPadicBoundedWittComparison.ringFun D w x) := by
  rw [ringEquiv_toCarrier]
  exact carrierRingEquiv_originalInclusion_val D w x

def radiusMap (ρ : PadicWittRhoCompletion.Radius) :
    ActualCompleted D w →+* PadicWittRhoCompletion.Completed (Arithmetic.residueChar w.1) ρ :=
  (PadicWittFrechetComparison.radiusMap (Arithmetic.residueChar w.1) ρ).comp
    (ringEquiv D w).toRingHom

theorem radiusMap_continuous (ρ : PadicWittRhoCompletion.Radius) :
    Continuous (radiusMap D w ρ) :=
  (PadicWittFrechetComparison.radiusMap_continuous (Arithmetic.residueChar w.1) ρ).comp
    (ringEquiv_continuous D w)

theorem radiusMap_eq_completedRingEquiv (ρ : PadicWittRhoCompletion.Radius)
    (x : ActualCompleted D w) :
    radiusMap D w ρ x =
      InitialThetaPadicWittRhoCompletionComparison.completedRingEquiv D w ρ
        (InitialThetaWittFrechetComparison.radiusMap D w
          (InitialThetaPadicWittRhoCompletionComparison.actualRadius D w ρ) x) := by
  change PadicWittAllRadiusCompletion.evaluate (Arithmetic.residueChar w.1) ρ
      (PadicWittFrechetComparison.ringEquiv (Arithmetic.residueChar w.1)
        (ringEquiv D w x)) = _
  rw [ringEquiv_toCarrier]
  exact InitialThetaPadicWittAllRadiusComparison.evaluate_ringEquiv D w ρ
    (InitialThetaWittFrechetComparison.ringEquiv D w x)

theorem norm_radiusMap_pow (ρ : PadicWittRhoCompletion.Radius)
    (x : ActualCompleted D w) :
    ‖radiusMap D w ρ x‖ ^ Arithmetic.localDeg w.1 =
      ‖InitialThetaWittFrechetComparison.radiusMap D w
        (InitialThetaPadicWittRhoCompletionComparison.actualRadius D w ρ) x‖ := by
  rw [radiusMap_eq_completedRingEquiv]
  exact InitialThetaPadicWittRhoCompletionComparison.completedRingEquiv_norm_pow D w ρ _

theorem tendsto_iff_radiusMaps {ι : Type*} (l : Filter ι)
    (f : ι → ActualCompleted D w) (x : ActualCompleted D w) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ ρ : PadicWittRhoCompletion.Radius,
      Filter.Tendsto (fun i => radiusMap D w ρ (f i)) l (𝓝 (radiusMap D w ρ x)) := by
  rw [(homeomorph D w).isInducing.tendsto_nhds_iff,
    PadicWittFrechetComparison.tendsto_iff_radiusMaps]
  rfl

theorem tendsto_iff_rationalRadiusMaps {ι : Type*} (l : Filter ι)
    (f : ι → ActualCompleted D w) (x : ActualCompleted D w) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ q : PadicWittRationalRadiusTopology.RationalRadius,
      Filter.Tendsto
        (fun i => radiusMap D w (PadicWittRationalRadiusTopology.toRadius q) (f i)) l
        (𝓝 (radiusMap D w (PadicWittRationalRadiusTopology.toRadius q) x)) := by
  rw [(homeomorph D w).isInducing.tendsto_nhds_iff,
    PadicWittFrechetTopology.tendsto_iff_rationalRadiusMaps]
  rfl

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittFrechetComparison
