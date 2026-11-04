import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoCompletion
import Mathlib.Topology.Algebra.Ring.Basic

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-ALL-RADIUS-COMPLETION
source: Joshi II `se:ff-rings`, the family of rho norms used in
`pr:teichmuller-lift-A/B`, and completion of the independent standard
bounded Witt period subring.
fidelity: takes the closure of the standard p-only bounded Witt localization's
diagonal image in the product of all fixed-radius completions. It constructs
a complete Hausdorff topological ring, an injective dense original-ring map,
and coordinate seminorms with the original standard rho values. Every
declaration depends only on p and its primality instance.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the comparison with the actual all-radius carrier,
paper B, scalar structures and period/BK identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.PadicWittAllRadiusCompletion

open scoped ENNReal Topology
noncomputable section

variable (p : ℕ) [Fact p.Prime]

abbrev Radius := PadicWittRhoCompletion.Radius
abbrev Product := ∀ ρ : Radius, PadicWittRhoCompletion.Completed p ρ

def diagonal : PadicBoundedWittLocalization.Ring p →+* Product p :=
  RingHom.pi (PadicWittRhoCompletion.inclusion p)

def commonSubring : Subring (Product p) := (diagonal p).range.topologicalClosure

abbrev Carrier := ↥(commonSubring p)

instance carrierComplete : CompleteSpace (Carrier p) :=
  (Subring.isClosed_topologicalClosure (diagonal p).range).isComplete.completeSpace_coe

theorem carrier_isTopologicalRing : IsTopologicalRing (Carrier p) := inferInstance

theorem carrier_isHausdorff : T2Space (Carrier p) := inferInstance

def inclusion : PadicBoundedWittLocalization.Ring p →+* Carrier p :=
  (diagonal p).codRestrict (commonSubring p)
    (fun x => Subring.le_topologicalClosure _ ⟨x, rfl⟩)

def evaluate (ρ : Radius) : Carrier p →+* PadicWittRhoCompletion.Completed p ρ :=
  (Pi.evalRingHom (fun r => PadicWittRhoCompletion.Completed p r) ρ).comp
    (commonSubring p).subtype

theorem evaluate_inclusion (ρ : Radius) (x : PadicBoundedWittLocalization.Ring p) :
    evaluate p ρ (inclusion p x) = PadicWittRhoCompletion.inclusion p ρ x := rfl

theorem inclusion_injective : Function.Injective (inclusion p) := by
  let r : Radius := ⟨ENNReal.ofReal (1 / 2 : ℝ), by constructor <;> norm_num⟩
  intro x y h
  apply PadicWittRhoCompletion.inclusion_injective p r
  exact congrArg (evaluate p r) h

theorem inclusion_denseRange : DenseRange (inclusion p) := by
  apply Subtype.dense_iff.mpr
  rw [← Set.range_comp]
  change (commonSubring p : Set (Product p)) ⊆
    closure (Set.range (diagonal p))
  exact Set.Subset.rfl

theorem evaluate_continuous (ρ : Radius) : Continuous (evaluate p ρ) :=
  (continuous_apply ρ).comp continuous_subtype_val

@[ext]
theorem ext {x y : Carrier p} (h : ∀ ρ : Radius, evaluate p ρ x = evaluate p ρ y) :
    x = y := Subtype.ext (funext h)

def coordinateSeminorm (ρ : Radius) : RingSeminorm (Carrier p) where
  toFun x := ‖evaluate p ρ x‖
  map_zero' := by rw [map_zero, norm_zero]
  add_le' x y := by rw [map_add]; exact norm_add_le _ _
  neg' x := by rw [map_neg, norm_neg]
  mul_le' x y := by rw [map_mul]; exact norm_mul_le _ _

theorem coordinateSeminorm_continuous (ρ : Radius) :
    Continuous (coordinateSeminorm p ρ) := (evaluate_continuous p ρ).norm

theorem coordinateSeminorm_inclusion (ρ : Radius)
    (x : PadicBoundedWittLocalization.Ring p) :
    coordinateSeminorm p ρ (inclusion p x) =
      PadicWittRhoNorm.realValue p ρ.val x :=
  PadicWittRhoCompletion.inclusion_norm p ρ x

theorem coordinateSeminorm_prime (ρ : Radius) :
    coordinateSeminorm p ρ (inclusion p p) = ρ.val.toReal :=
  PadicWittRhoCompletion.inclusion_prime_norm p ρ

theorem coordinates_separate_zero (x : Carrier p) :
    (∀ ρ : Radius, coordinateSeminorm p ρ x = 0) ↔ x = 0 := by
  constructor
  · intro hx
    apply ext p
    intro ρ
    rw [map_zero]
    exact norm_eq_zero.mp (hx ρ)
  · rintro rfl
    intro ρ
    exact map_zero _

theorem tendsto_iff_coordinates {ι : Type*} (l : Filter ι) (f : ι → Carrier p)
    (x : Carrier p) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ ρ : Radius,
      Filter.Tendsto (fun i => evaluate p ρ (f i)) l (𝓝 (evaluate p ρ x)) := by
  rw [tendsto_subtype_rng, tendsto_pi_nhds]
  rfl

end
end JoshiTeich.Act1Scene1.PadicWittAllRadiusCompletion
