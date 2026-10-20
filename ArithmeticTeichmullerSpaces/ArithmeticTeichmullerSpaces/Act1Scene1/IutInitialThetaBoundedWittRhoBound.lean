import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittExpansionOperations

/-!
source-id: JT-SCENE1-INITIAL-THETA-BOUNDED-WITT-RHO-BOUND
source: Joshi II se:ff-rings / W(O_F) into B (511--512, 719--727), and
the rho-weighted coefficient bounds used for the Frechet B norms in Joshi
Teichmuller Spaces 2, §7--§9.
fidelity: records the explicit finite rho-weighted bound on the genuine
Teichmuller digits of an actual bounded Witt expansion. For 0 ≤ rho ≤ 1 this
bound follows from the existing uniform digit bound, and at rho = 1 it is
equivalent to the existing bounded-expansion witness. This is only a
rho-bound predicate; it does not define a numerical seminorm, a Frechet
completion, or the paper's completed B. Original proofs; Scene1/Derived;
Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaBoundedWittRhoBound

open JoshiTeich.Prologue InitialThetaTiltFontaine InitialThetaCanonicalGeometricFontaine
open InitialThetaBoundedWittLocalization
open InitialThetaBoundedWittExpansion
open WittTeichmullerExpansion
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrimeRho : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def HasRhoBoundedExpansion (rho : ℝ) (z : Ambient D w) : Prop :=
  ∃ m : ℕ, ∃ y : FieldWitt D w, ∃ c : ℕ → InitialThetaTiltField.Carrier D w,
    ∃ C : ℝ, 0 < C ∧ (∀ n : ℕ, ‖c n‖ ≤ C) ∧
      Expands (Arithmetic.residueChar w.1) y c ∧
      z * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
        algebraMap (FieldWitt D w) (Ambient D w) y ∧
      (∀ n : ℕ, ‖c n‖ * rho ^ n ≤ C)

theorem hasRhoBoundedExpansion_of_hasBoundedExpansion
    (rho : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (z : Ambient D w) (hz : HasBoundedExpansion D w z) :
    HasRhoBoundedExpansion D w rho z := by
  obtain ⟨m, y, c, C, hC, hbound, hc, hz⟩ := hz
  refine ⟨m, y, c, C, hC, hbound, hc, hz, ?_⟩
  intro n
  have hpow : rho ^ n ≤ 1 := pow_le_one₀ hrho0 hrho1
  exact (mul_le_of_le_one_right (norm_nonneg _) hpow).trans (hbound n)

theorem hasBoundedExpansion_of_hasRhoBoundedExpansion_one
    (z : Ambient D w) (hz : HasRhoBoundedExpansion D w 1 z) :
    HasBoundedExpansion D w z := by
  obtain ⟨m, y, c, C, hC, hbound, hc, hz, _⟩ := hz
  exact ⟨m, y, c, C, hC, hbound, hc, hz⟩

theorem hasRhoBoundedExpansion_teichmuller_mul
    (rho : ℝ) (z : Ambient D w) (hz : HasRhoBoundedExpansion D w rho z)
    (r : InitialThetaTiltField.Carrier D w) (hr : r ≠ 0) :
    HasRhoBoundedExpansion D w rho
      (algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z) := by
  obtain ⟨m, y, c, C, hC, hbound, hc, hz, hrho⟩ := hz
  let p := Arithmetic.residueChar w.1
  let y' : FieldWitt D w := WittVector.teichmuller p r * y
  let c' : ℕ → InitialThetaTiltField.Carrier D w := fun n => r * c n
  refine ⟨m, y', c', ‖r‖ * C, mul_pos (norm_pos_iff.mpr hr) hC, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg r)
  · exact expands_teichmuller_mul p r y c hc
  · calc
      (algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller p r) * z) * (p : Ambient D w) ^ m =
        algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller p r) * (z * (p : Ambient D w) ^ m) := by
            rw [mul_assoc]
      _ = algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller p r) *
            algebraMap (FieldWitt D w) (Ambient D w) y := by rw [hz]
      _ = algebraMap (FieldWitt D w) (Ambient D w) y' := by rw [map_mul]
  · intro n
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hrho n) (norm_nonneg r)

theorem hasRhoBoundedExpansion_teichmuller_mul_iff
    (rho : ℝ) (z : Ambient D w) (r : InitialThetaTiltField.Carrier D w)
    (hr : r ≠ 0) :
    HasRhoBoundedExpansion D w rho
        (algebraMap (FieldWitt D w) (Ambient D w)
            (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z) ↔
      HasRhoBoundedExpansion D w rho z := by
  constructor
  · intro hz
    have hscaled := hasRhoBoundedExpansion_teichmuller_mul D w rho
      (algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z)
      hz r⁻¹ (inv_ne_zero hr)
    have heq :
        algebraMap (FieldWitt D w) (Ambient D w)
            (WittVector.teichmuller (Arithmetic.residueChar w.1) r⁻¹) *
          (algebraMap (FieldWitt D w) (Ambient D w)
            (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z) = z := by
      rw [← mul_assoc, ← map_mul, ← (WittVector.teichmuller (Arithmetic.residueChar w.1)).map_mul,
        inv_mul_cancel₀ hr, (WittVector.teichmuller (Arithmetic.residueChar w.1)).map_one,
        map_one, one_mul]
    rw [heq] at hscaled
    exact hscaled
  · intro hz
    exact hasRhoBoundedExpansion_teichmuller_mul D w rho z hz r hr

theorem hasRhoBoundedExpansion_mono
    (rho₁ rho₂ : ℝ) (h₁ : 0 ≤ rho₁) (h₂ : rho₁ ≤ rho₂)
    (z : Ambient D w) (hz : HasRhoBoundedExpansion D w rho₂ z) :
    HasRhoBoundedExpansion D w rho₁ z := by
  obtain ⟨m, y, c, C, hC, hbound, hc, hz, hrho⟩ := hz
  refine ⟨m, y, c, C, hC, hbound, hc, hz, ?_⟩
  intro n
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ h₁ h₂ n) (norm_nonneg _)).trans (hrho n)

theorem hasRhoBoundedExpansion_toAmbient
    (rho : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    HasRhoBoundedExpansion D w rho (toAmbient D w x) :=
  hasRhoBoundedExpansion_of_hasBoundedExpansion D w rho hrho0 hrho1
    (toAmbient D w x) (hasBoundedExpansion D w x)

theorem range_eq_rhoBoundedExpansions_one :
    Set.range (toAmbient D w) =
      {z | HasRhoBoundedExpansion D w 1 z} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact hasRhoBoundedExpansion_toAmbient D w 1 (by norm_num) (by norm_num) x
  · intro hz
    rw [range_eq_boundedExpansions D w]
    exact hasBoundedExpansion_of_hasRhoBoundedExpansion_one D w z hz

end
end JoshiTeich.Act1Scene1.InitialThetaBoundedWittRhoBound
