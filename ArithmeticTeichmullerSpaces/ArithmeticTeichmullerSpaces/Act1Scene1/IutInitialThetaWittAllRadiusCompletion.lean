import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoCompletion
import Mathlib.Topology.Algebra.Ring.Basic

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ALL-RADIUS-COMPLETION
source: Joshi II `se:ff-rings`, the family of rho norms used in
`pr:teichmuller-lift-A/B`, and completion of the bounded period subring.
fidelity: takes the closure of the same bounded Witt localization's
diagonal image in the product of all its fixed-radius completions.
Constructs a complete Hausdorff topological ring, an injective dense
original-ring map, and continuous coordinate seminorms with the original
rho values. Convergence is exactly convergence in every radius.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; metrizability, the Frechet algebra and scalar
structures, multiplicative equality, Frobenius and period/BK identities
remain open. The construction is not declared to be the paper B.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittAllRadiusCompletion

open JoshiTeich.Prologue
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

abbrev Radius := InitialThetaWittRhoCompletion.Radius
abbrev Product := ∀ ρ : Radius, InitialThetaWittRhoCompletion.Completed D w ρ

def diagonal : InitialThetaBoundedWittLocalization.Ring D w →+* Product D w :=
  RingHom.pi (InitialThetaWittRhoCompletion.inclusion D w)

def commonSubring : Subring (Product D w) := (diagonal D w).range.topologicalClosure

abbrev Carrier := ↥(commonSubring D w)

instance carrierComplete : CompleteSpace (Carrier D w) :=
  (Subring.isClosed_topologicalClosure (diagonal D w).range).isComplete.completeSpace_coe

theorem carrier_isTopologicalRing : IsTopologicalRing (Carrier D w) := inferInstance

theorem carrier_isHausdorff : T2Space (Carrier D w) := inferInstance

def inclusion : InitialThetaBoundedWittLocalization.Ring D w →+* Carrier D w :=
  (diagonal D w).codRestrict (commonSubring D w)
    (fun x => Subring.le_topologicalClosure _ ⟨x, rfl⟩)

def evaluate (ρ : Radius) : Carrier D w →+* InitialThetaWittRhoCompletion.Completed D w ρ :=
  (Pi.evalRingHom (fun r => InitialThetaWittRhoCompletion.Completed D w r) ρ).comp
    (commonSubring D w).subtype

theorem evaluate_inclusion (ρ : Radius) (x : InitialThetaBoundedWittLocalization.Ring D w) :
    evaluate D w ρ (inclusion D w x) = InitialThetaWittRhoCompletion.inclusion D w ρ x := rfl

theorem inclusion_injective : Function.Injective (inclusion D w) := by
  let r : Radius := ⟨ENNReal.ofReal (1 / 2 : ℝ), by constructor <;> norm_num⟩
  intro x y h
  apply InitialThetaWittRhoCompletion.inclusion_injective D w r
  exact congrArg (evaluate D w r) h

theorem inclusion_denseRange : DenseRange (inclusion D w) := by
  apply Subtype.dense_iff.mpr
  rw [← Set.range_comp]
  change (commonSubring D w : Set (Product D w)) ⊆
    closure (Set.range (diagonal D w))
  exact Set.Subset.rfl

theorem evaluate_continuous (ρ : Radius) : Continuous (evaluate D w ρ) :=
  (continuous_apply ρ).comp continuous_subtype_val

@[ext]
theorem ext {x y : Carrier D w} (h : ∀ ρ : Radius, evaluate D w ρ x = evaluate D w ρ y) :
    x = y := Subtype.ext (funext h)

def coordinateSeminorm (ρ : Radius) : RingSeminorm (Carrier D w) where
  toFun x := ‖evaluate D w ρ x‖
  map_zero' := by rw [map_zero, norm_zero]
  add_le' x y := by rw [map_add]; exact norm_add_le _ _
  neg' x := by rw [map_neg, norm_neg]
  mul_le' x y := by rw [map_mul]; exact norm_mul_le _ _

theorem coordinateSeminorm_continuous (ρ : Radius) :
    Continuous (coordinateSeminorm D w ρ) := (evaluate_continuous D w ρ).norm

theorem coordinateSeminorm_inclusion (ρ : Radius)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    coordinateSeminorm D w ρ (inclusion D w x) =
      InitialThetaWittRhoNorm.realValue D w ρ.val x :=
  InitialThetaWittRhoCompletion.inclusion_norm D w ρ x

theorem coordinateSeminorm_prime (ρ : Radius) :
    coordinateSeminorm D w ρ (inclusion D w (Arithmetic.residueChar w.1)) = ρ.val.toReal :=
  InitialThetaWittRhoCompletion.inclusion_prime_norm D w ρ

theorem coordinates_separate_zero (x : Carrier D w) :
    (∀ ρ : Radius, coordinateSeminorm D w ρ x = 0) ↔ x = 0 := by
  constructor
  · intro hx
    apply ext D w
    intro ρ
    rw [map_zero]
    exact norm_eq_zero.mp (hx ρ)
  · rintro rfl
    intro ρ
    exact map_zero _

theorem tendsto_iff_coordinates {ι : Type*} (l : Filter ι) (f : ι → Carrier D w)
    (x : Carrier D w) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ ρ : Radius,
      Filter.Tendsto (fun i => evaluate D w ρ (f i)) l (𝓝 (evaluate D w ρ x)) := by
  rw [tendsto_subtype_rng, tendsto_pi_nhds]
  rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittAllRadiusCompletion
