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

def RhoBoundSet (rho : ℝ) (z : Ambient D w) : Set ℝ :=
  {C | ∃ m : ℕ, ∃ y : FieldWitt D w,
    ∃ c : ℕ → InitialThetaTiltField.Carrier D w,
      0 < C ∧ (∀ n : ℕ, ‖c n‖ ≤ C) ∧
        Expands (Arithmetic.residueChar w.1) y c ∧
        z * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
          algebraMap (FieldWitt D w) (Ambient D w) y ∧
        (∀ n : ℕ, ‖c n‖ * rho ^ n ≤ C)}

noncomputable def rhoInfimum (rho : ℝ) (z : Ambient D w) : ℝ :=
  sInf (RhoBoundSet D w rho z)

theorem hasRhoBoundedExpansion_iff_rhoBoundSet_nonempty
    (rho : ℝ) (z : Ambient D w) :
    HasRhoBoundedExpansion D w rho z ↔ (RhoBoundSet D w rho z).Nonempty := by
  constructor
  · rintro ⟨m, y, c, C, hC, hbound, hc, hz, hrho⟩
    exact ⟨C, ⟨m, y, c, hC, hbound, hc, hz, hrho⟩⟩
  · rintro ⟨C, ⟨m, y, c, hC, hbound, hc, hz, hrho⟩⟩
    exact ⟨m, y, c, C, hC, hbound, hc, hz, hrho⟩

theorem rhoBoundSet_lowerBound_zero
    (rho : ℝ) (z : Ambient D w) :
    ∀ C ∈ RhoBoundSet D w rho z, 0 ≤ C := by
  intro C hC
  rcases hC with ⟨m, y, c, hC, hbound, hc, hz, hrho⟩
  exact hC.le

theorem rhoBoundSet_upward_closed
    (rho : ℝ) (z : Ambient D w) {C C' : ℝ}
    (hC : C ∈ RhoBoundSet D w rho z) (hCC' : C ≤ C') :
    C' ∈ RhoBoundSet D w rho z := by
  rcases hC with ⟨m, y, c, hpos, hbound, hc, hz, hrho⟩
  refine ⟨m, y, c, lt_of_lt_of_le hpos hCC', ?_, hc, hz, ?_⟩
  · intro n
    exact (hbound n).trans hCC'
  · intro n
    exact (hrho n).trans hCC'

theorem rhoInfimum_nonneg
    (rho : ℝ) (z : Ambient D w)
    (hset : (RhoBoundSet D w rho z).Nonempty) :
    0 ≤ rhoInfimum D w rho z := by
  unfold rhoInfimum
  apply le_csInf hset
  intro C hC
  exact rhoBoundSet_lowerBound_zero D w rho z C hC

theorem rhoInfimum_le_of_mem
    (rho : ℝ) (z : Ambient D w) {C : ℝ}
    (hC : C ∈ RhoBoundSet D w rho z) :
    rhoInfimum D w rho z ≤ C := by
  unfold rhoInfimum
  apply csInf_le
  · exact ⟨0, rhoBoundSet_lowerBound_zero D w rho z⟩
  · exact hC

theorem rhoInfimum_mono
    (rho₁ rho₂ : ℝ) (h₁ : 0 ≤ rho₁) (h₂ : rho₁ ≤ rho₂)
    (z : Ambient D w) (hset₂ : (RhoBoundSet D w rho₂ z).Nonempty) :
    rhoInfimum D w rho₁ z ≤ rhoInfimum D w rho₂ z := by
  unfold rhoInfimum
  apply le_csInf hset₂
  intro C hC
  rcases hC with ⟨m, y, c, hpos, hbound, hc, hz, hrho⟩
  have hC₁ : C ∈ RhoBoundSet D w rho₁ z := by
    refine ⟨m, y, c, hpos, hbound, hc, hz, ?_⟩
    intro n
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ h₁ h₂ n) (norm_nonneg _)).trans (hrho n)
  exact rhoInfimum_le_of_mem D w rho₁ z hC₁

theorem rhoBoundSet_zero_eq_one (z : Ambient D w) :
    RhoBoundSet D w 0 z = RhoBoundSet D w 1 z := by
  ext C
  constructor
  · rintro ⟨m, y, c, hpos, hbound, hc, hz, hrho⟩
    refine ⟨m, y, c, hpos, hbound, hc, hz, ?_⟩
    intro n
    simpa using hbound n
  · rintro ⟨m, y, c, hpos, hbound, hc, hz, hrho⟩
    refine ⟨m, y, c, hpos, hbound, hc, hz, ?_⟩
    intro n
    by_cases hn : n = 0
    · subst n
      simpa using hbound 0
    · simpa [hn] using hpos.le

theorem rhoInfimum_zero_eq_one (z : Ambient D w) :
    rhoInfimum D w 0 z = rhoInfimum D w 1 z := by
  rw [rhoInfimum, rhoInfimum, rhoBoundSet_zero_eq_one D w z]

theorem rhoBoundSet_teichmuller_mul_mem
    (rho : ℝ) (z : Ambient D w) (r : InitialThetaTiltField.Carrier D w)
    (hr : r ≠ 0) {C : ℝ} (hC : C ∈ RhoBoundSet D w rho z) :
    ‖r‖ * C ∈ RhoBoundSet D w rho
      (algebraMap (FieldWitt D w) (Ambient D w)
        (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z) := by
  rcases hC with ⟨m, y, c, hpos, hbound, hc, hz, hrho⟩
  let p := Arithmetic.residueChar w.1
  let y' : FieldWitt D w := WittVector.teichmuller p r * y
  let c' : ℕ → InitialThetaTiltField.Carrier D w := fun n => r * c n
  refine ⟨m, y', c', mul_pos (norm_pos_iff.mpr hr) hpos, ?_, ?_, ?_, ?_⟩
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

theorem rhoInfimum_teichmuller_mul_le_of_mem
    (rho : ℝ) (z : Ambient D w) (r : InitialThetaTiltField.Carrier D w)
    (hr : r ≠ 0) {C : ℝ} (hC : C ∈ RhoBoundSet D w rho z) :
    rhoInfimum D w rho
      (algebraMap (FieldWitt D w) (Ambient D w)
        (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z) ≤ ‖r‖ * C :=
  rhoInfimum_le_of_mem D w rho
    (algebraMap (FieldWitt D w) (Ambient D w)
      (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z)
    (rhoBoundSet_teichmuller_mul_mem D w rho z r hr hC)

theorem rhoInfimum_teichmuller_mul_ge_of_nonempty
    (rho : ℝ) (z : Ambient D w) (r : InitialThetaTiltField.Carrier D w)
    (hr : r ≠ 0)
    (hset : (RhoBoundSet D w rho
      (algebraMap (FieldWitt D w) (Ambient D w)
        (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z)).Nonempty) :
    ‖r‖ * rhoInfimum D w rho z ≤
      rhoInfimum D w rho
        (algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z) := by
  unfold rhoInfimum
  apply le_csInf hset
  intro C hC
  have hinv := rhoBoundSet_teichmuller_mul_mem D w rho
    (algebraMap (FieldWitt D w) (Ambient D w)
      (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z)
    r⁻¹ (inv_ne_zero hr) hC
  have heq :
      algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller (Arithmetic.residueChar w.1) r⁻¹) *
        (algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z) = z := by
    rw [← mul_assoc, ← map_mul, ← (WittVector.teichmuller (Arithmetic.residueChar w.1)).map_mul,
      inv_mul_cancel₀ hr, (WittVector.teichmuller (Arithmetic.residueChar w.1)).map_one,
      map_one, one_mul]
  rw [heq] at hinv
  have hi := rhoInfimum_le_of_mem D w rho z hinv
  calc
    ‖r‖ * rhoInfimum D w rho z ≤
        ‖r‖ * (‖r⁻¹‖ * C) :=
      mul_le_mul_of_nonneg_left hi (norm_nonneg _)
    _ = C := by
      rw [← mul_assoc, ← norm_mul, mul_inv_cancel₀ hr, norm_one, one_mul]

theorem rhoInfimum_teichmuller_mul_eq_of_nonempty
    (rho : ℝ) (z : Ambient D w) (r : InitialThetaTiltField.Carrier D w)
    (hr : r ≠ 0) (hset : (RhoBoundSet D w rho z).Nonempty) :
    rhoInfimum D w rho
        (algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z) =
      ‖r‖ * rhoInfimum D w rho z := by
  let z' : Ambient D w :=
    algebraMap (FieldWitt D w) (Ambient D w)
      (WittVector.teichmuller (Arithmetic.residueChar w.1) r) * z
  change rhoInfimum D w rho z' = ‖r‖ * rhoInfimum D w rho z
  have hset' : (RhoBoundSet D w rho z').Nonempty := by
    rcases hset with ⟨C, hC⟩
    exact ⟨‖r‖ * C, by
      exact rhoBoundSet_teichmuller_mul_mem D w rho z r hr hC⟩
  have hge := rhoInfimum_teichmuller_mul_ge_of_nonempty D w rho z r hr hset'
  have heq :
      algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller (Arithmetic.residueChar w.1) r⁻¹) * z' = z := by
    dsimp [z']
    rw [← mul_assoc, ← map_mul, ← (WittVector.teichmuller (Arithmetic.residueChar w.1)).map_mul,
      inv_mul_cancel₀ hr, (WittVector.teichmuller (Arithmetic.residueChar w.1)).map_one,
      map_one, one_mul]
  have hset_rev :
      (RhoBoundSet D w rho
        (algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller (Arithmetic.residueChar w.1) r⁻¹) * z')).Nonempty := by
    rw [heq]
    exact hset
  have hrev := rhoInfimum_teichmuller_mul_ge_of_nonempty D w rho z' r⁻¹
    (inv_ne_zero hr) hset_rev
  rw [heq] at hrev
  apply le_antisymm
  · calc
      rhoInfimum D w rho z' =
          ‖r‖ * (‖r⁻¹‖ * rhoInfimum D w rho z') := by
            rw [← mul_assoc, ← norm_mul, mul_inv_cancel₀ hr, norm_one, one_mul]
      _ ≤ ‖r‖ * rhoInfimum D w rho z :=
        mul_le_mul_of_nonneg_left hrev (norm_nonneg _)
  · exact hge

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

theorem hasRhoBoundedExpansion_one_iff
    (z : Ambient D w) :
    HasRhoBoundedExpansion D w 1 z ↔ HasBoundedExpansion D w z := by
  constructor
  · exact hasBoundedExpansion_of_hasRhoBoundedExpansion_one D w z
  · intro hz
    exact hasRhoBoundedExpansion_of_hasBoundedExpansion D w 1 (by norm_num) (by norm_num)
      z hz

theorem hasRhoBoundedExpansion_zero_iff
    (z : Ambient D w) :
    HasRhoBoundedExpansion D w 0 z ↔ HasBoundedExpansion D w z := by
  constructor
  · intro hz
    obtain ⟨m, y, c, C, hC, hbound, hc, hz, _⟩ := hz
    exact ⟨m, y, c, C, hC, hbound, hc, hz⟩
  · intro hz
    exact hasRhoBoundedExpansion_of_hasBoundedExpansion D w 0 (by norm_num) (by norm_num)
      z hz

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

theorem rhoInfimum_teichmuller_mul_eq_toAmbient
    (rho : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (x : InitialThetaBoundedWittLocalization.Ring D w)
    (r : InitialThetaTiltField.Carrier D w) (hr : r ≠ 0) :
    rhoInfimum D w rho
        (algebraMap (FieldWitt D w) (Ambient D w)
          (WittVector.teichmuller (Arithmetic.residueChar w.1) r) *
          toAmbient D w x) =
      ‖r‖ * rhoInfimum D w rho (toAmbient D w x) := by
  apply rhoInfimum_teichmuller_mul_eq_of_nonempty D w rho (toAmbient D w x) r hr
  apply (hasRhoBoundedExpansion_iff_rhoBoundSet_nonempty D w rho
    (toAmbient D w x)).mp
  exact hasRhoBoundedExpansion_toAmbient D w rho hrho0 hrho1 x

end
end JoshiTeich.Act1Scene1.InitialThetaBoundedWittRhoBound
