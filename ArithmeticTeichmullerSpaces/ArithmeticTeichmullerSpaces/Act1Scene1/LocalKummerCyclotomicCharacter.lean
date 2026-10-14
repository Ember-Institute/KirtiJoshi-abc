import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerTateBasis
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerPadicCohomology
import Mathlib.Topology.Algebra.Group.Units

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-CYCLOTOMIC-CHARACTER
source: the Galois action on Z_p(1), Joshi III (3190--3236).
fidelity: derives the continuous unit-valued character from the actual Tate
action and proves its scalar action formula. No character is supplied by a caller.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.Cyclotomic
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]

def coefficient (σ : Ω ≃ₐ[K] Ω) : ℤ_[p] :=
  (TateBasis.equiv (p := p) (Ω := Ω)).symm
    (padicTateRepresentation p σ (TateBasis.equiv (p := p) (Ω := Ω) 1))

theorem coordinate_action (σ : Ω ≃ₐ[K] Ω) (x : Additive (cyclotomicTateGroup p Ω)) :
    (TateBasis.equiv (p := p) (Ω := Ω)).symm (padicTateRepresentation p σ x) =
      coefficient p σ * (TateBasis.equiv (p := p) (Ω := Ω)).symm x := by
  let e := TateBasis.equiv (p := p) (Ω := Ω)
  have hx : x = e.symm x • e 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, e.apply_symm_apply]
  calc
    e.symm (padicTateRepresentation p σ x) =
        e.symm (padicTateRepresentation p σ (e.symm x • e 1)) :=
      congrArg (fun y => e.symm (padicTateRepresentation p σ y)) hx
    _ = e.symm x • e.symm (padicTateRepresentation p σ (e 1)) := by
      rw [map_smul, map_smul]
    _ = coefficient p σ * e.symm x := mul_comm _ _

theorem coefficient_one : coefficient (K := K) (Ω := Ω) p 1 = 1 := by
  unfold coefficient
  rw [map_one]
  exact (TateBasis.equiv (p := p) (Ω := Ω)).symm_apply_apply 1

theorem coefficient_mul (σ τ : Ω ≃ₐ[K] Ω) :
    coefficient p (σ * τ) = coefficient p σ * coefficient p τ := by
  unfold coefficient at ⊢
  rw [map_mul]
  exact coordinate_action p σ _

def character : (Ω ≃ₐ[K] Ω) →* ℤ_[p]ˣ where
  toFun σ := Units.mkOfMulEqOne (coefficient p σ) (coefficient p σ⁻¹) (by
    rw [← coefficient_mul, mul_inv_cancel, coefficient_one])
  map_one' := Units.ext (coefficient_one p)
  map_mul' σ τ := Units.ext (coefficient_mul p σ τ)

theorem character_val (σ : Ω ≃ₐ[K] Ω) :
    (character p σ : ℤ_[p]) = coefficient p σ := rfl

theorem continuous_coefficient : Continuous (coefficient (K := K) (Ω := Ω) p) := by
  apply (TateBasis.equiv (p := p) (Ω := Ω)).symm.continuous.comp
  exact continuous_ofMul.comp ((continuous_tateAction p).comp
    (show Continuous (fun σ : Ω ≃ₐ[K] Ω =>
      (σ, (TateBasis.equiv (p := p) (Ω := Ω) 1).toMul)) from
      continuous_id.prodMk continuous_const))

theorem continuous_character : Continuous (character (K := K) (Ω := Ω) p) :=
  Units.continuous_iff.mpr
    ⟨continuous_coefficient p, (continuous_coefficient p).comp continuous_inv⟩

theorem coordinate_action_character (σ : Ω ≃ₐ[K] Ω)
    (x : Additive (cyclotomicTateGroup p Ω)) :
    (TateBasis.equiv (p := p) (Ω := Ω)).symm (padicTateRepresentation p σ x) =
      (character p σ : ℤ_[p]) * (TateBasis.equiv (p := p) (Ω := Ω)).symm x :=
  coordinate_action p σ x

end
end JoshiTeich.Act1Scene1.LocalKummer.Cyclotomic
