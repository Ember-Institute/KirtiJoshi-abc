import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerRootTower
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Group.Basic

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-CONTINUITY
source: Joshi III compatible local Kummer roots (3190--3208), with the
Krull topology on the Galois group and inverse-limit topology on roots of unity.
fidelity: proves local constancy at each level and continuity of the entire
Kummer cocycle into the compatible-sequence group, using discrete units
at each level and the product subspace topology. The coefficient action is
jointly continuous. Continuous cohomology and H^1_e/BK comparison remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v w
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]

/-- Only the finite-level coefficient units carry the discrete topology. -/
local instance levelUnitsTopology : TopologicalSpace Ωˣ := ⊥
local instance levelUnitsDiscrete : DiscreteTopology Ωˣ := ⟨rfl⟩

instance cyclotomicTateTopology (p : ℕ) : TopologicalSpace (cyclotomicTateGroup p Ω) :=
  TopologicalSpace.induced (fun x => x.1) inferInstance

instance cyclotomicTateIsTopologicalGroup (p : ℕ) :
    IsTopologicalGroup (cyclotomicTateGroup p Ω) :=
  topologicalGroup_induced (cyclotomicTateGroup p Ω).subtype

theorem continuous_tate_iff_level_locallyConstant
    {X : Type w} [TopologicalSpace X] {p : ℕ} (f : X → cyclotomicTateGroup p Ω) :
    Continuous f ↔ ∀ n, IsLocallyConstant (fun x => (f x).1 n) := by
  constructor
  · intro hf n
    exact (IsLocallyConstant.iff_continuous _).mpr
      ((continuous_apply n).comp (continuous_induced_rng.mp hf))
  · intro hf
    exact continuous_induced_rng.mpr (continuous_pi fun n => (hf n).continuous)

variable [Algebra.IsIntegral K Ω]

theorem galoisEval_isLocallyConstant (x : Ω) :
    IsLocallyConstant (fun σ : Ω ≃ₐ[K] Ω => σ x) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro σ
  let U := (fun τ : Ω ≃ₐ[K] Ω => σ⁻¹ * τ) ⁻¹'
    (MulAction.stabilizer (Ω ≃ₐ[K] Ω) x : Set (Ω ≃ₐ[K] Ω))
  refine ⟨U, (stabilizer_isOpen_of_isIntegral x).preimage
    (continuous_const.mul continuous_id), ?_, ?_⟩
  · change σ⁻¹ * σ ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  · intro τ hτ
    change σ.symm (τ x) = x at hτ
    have h := congrArg σ hτ
    simpa only [AlgEquiv.apply_symm_apply] using h

local instance levelUnitsContinuousSMul : ContinuousSMul (Ω ≃ₐ[K] Ω) Ωˣ := by
  apply (continuousSMul_iff_stabilizer_isOpen).mpr
  intro x
  have heq : (MulAction.stabilizer (Ω ≃ₐ[K] Ω) x : Set (Ω ≃ₐ[K] Ω)) =
      (MulAction.stabilizer (Ω ≃ₐ[K] Ω) (x : Ω) : Set (Ω ≃ₐ[K] Ω)) := by
    ext σ
    change σ • x = x ↔ σ (x : Ω) = (x : Ω)
    exact Units.ext_iff
  rw [heq]
  exact stabilizer_isOpen_of_isIntegral (x : Ω)

theorem continuous_tateAction (p : ℕ) :
    Continuous (fun z : (Ω ≃ₐ[K] Ω) × cyclotomicTateGroup p Ω => tateAction p z.1 z.2) := by
  apply (continuous_tate_iff_level_locallyConstant _).mpr
  intro n
  apply (IsLocallyConstant.iff_continuous _).mpr
  have heval : Continuous (fun x : cyclotomicTateGroup p Ω => x.1 n) :=
    (continuous_apply n).comp continuous_induced_dom
  exact continuous_fst.smul (heval.comp continuous_snd)

instance tateContinuousSMul (p : ℕ) :
    ContinuousSMul (Ω ≃ₐ[K] Ω) (cyclotomicTateGroup p Ω) := ⟨continuous_tateAction p⟩

namespace RootTower
variable {p : ℕ} {a : K} (R : RootTower (Ω := Ω) p a) (hp : 0 < p) (ha : a ≠ 0)

theorem ratio_isLocallyConstant (n : ℕ) :
    IsLocallyConstant (fun σ : Ω ≃ₐ[K] Ω => R.ratio σ n) :=
  (galoisEval_isLocallyConstant (R.root n)).comp (fun x => x / R.root n)

theorem character_isLocallyConstant (n : ℕ) :
    IsLocallyConstant (fun σ : Ω ≃ₐ[K] Ω => R.character hp ha σ n) :=
  IsLocallyConstant.desc _ (fun x : rootsOfUnity (p ^ n) Ω => (x.1 : Ω))
    (R.ratio_isLocallyConstant n) rootsOfUnity.coe_injective

theorem kummerCocycle_level_isLocallyConstant (n : ℕ) :
    IsLocallyConstant (fun σ : Ω ≃ₐ[K] Ω => (R.kummerCocycle hp ha σ).1 n) :=
  (R.character_isLocallyConstant hp ha n).comp Subtype.val

theorem continuous_kummerCocycle : Continuous (R.kummerCocycle hp ha) :=
  (continuous_tate_iff_level_locallyConstant _).mpr (R.kummerCocycle_level_isLocallyConstant hp ha)

def continuousCocycle : C((Ω ≃ₐ[K] Ω), cyclotomicTateGroup p Ω) :=
  ⟨R.kummerCocycle hp ha, R.continuous_kummerCocycle hp ha⟩

theorem continuousCocycle_isMulCocycle : groupCohomology.IsMulCocycle₁ (R.continuousCocycle hp ha) :=
  R.isMulCocycle_kummerCocycle hp ha

end RootTower
end
end JoshiTeich.Act1Scene1.LocalKummer
