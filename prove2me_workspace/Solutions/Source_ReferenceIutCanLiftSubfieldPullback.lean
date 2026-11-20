/-
Source: lana-agents/pi1 at ca7def953193f861a462aa0831eec8f0a31ff69f (Apache-2.0),
Pi1/Orbicurve/Pullback.lean, mul_div_eq_of_dvd and exists_pullback_subfield.
-/
import Solutions.Source_ReferenceIutCanLiftCompositumRamification
import Mathlib.FieldTheory.Normal.Closure

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open IntermediateField Ideal
open scoped IntermediateField.algebraAdjoinAdjoin

universe u

private theorem pullbackMultiplicity_mul {e₁ eA mA mB : ℕ}
    (hA : eA * mA = mB) (hpos : 0 < mB) (hdvd : eA * e₁ ∣ mB) :
    e₁ * (mB / (eA * e₁)) = mA := by
  rw [mul_comm eA] at hdvd ⊢
  subst mB
  have heA : 0 < eA := Nat.pos_of_ne_zero fun h => by simp [h] at hpos
  have h₁ : e₁ ∣ mA := by
    rw [mul_comm e₁] at hdvd
    exact (Nat.mul_dvd_mul_iff_left heA).mp hdvd
  rw [mul_comm e₁ eA, Nat.mul_div_mul_left _ _ heA, Nat.mul_div_cancel' h₁]

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  [CharZero k] [Normal (rationalBase k t) Ω]

/-- The compositum has closed-point multiplicities making its two projections
finite étale covers of subfield presentations. -/
theorem exists_pullback_subfield (ht : Transcendental k t)
    {B A Z : IntermediateField (rationalBase k t) Ω}
    [FiniteDimensional (rationalBase k t) B] [FiniteDimensional (rationalBase k t) A]
    [FiniteDimensional (rationalBase k t) Z]
    (hBA : B ≤ A) (hBZ : B ≤ Z) (mB : Ideal (coordRing t B) → ℕ)
    (mB_pos : ∀ v, v.IsMaximal → 0 < mB v)
    (mB_fin : {v : Ideal (coordRing t B) | v.IsMaximal ∧ mB v ≠ 1}.Finite)
    (mA : Ideal (coordRing t A) → ℕ) (mZ : Ideal (coordRing t Z) → ℕ)
    (hA : ∀ w : Ideal (coordRing t A), w.IsMaximal →
      ramificationIndex hBA w * mA w = mB (w.comap (ringMap hBA)))
    (hZ : ∀ w : Ideal (coordRing t Z), w.IsMaximal →
      ramificationIndex hBZ w * mZ w = mB (w.comap (ringMap hBZ))) :
    ∃ m : Ideal (coordRing t (Z ⊔ A)) → ℕ,
      (∀ w, w.IsMaximal → 0 < m w) ∧
      {w : Ideal (coordRing t (Z ⊔ A)) | w.IsMaximal ∧ m w ≠ 1}.Finite ∧
      (∀ w : Ideal (coordRing t (Z ⊔ A)), w.IsMaximal →
        ramificationIndex (le_sup_left : Z ≤ Z ⊔ A) w * m w =
          mZ (w.comap (ringMap le_sup_left))) ∧
      (∀ w : Ideal (coordRing t (Z ⊔ A)), w.IsMaximal →
        ramificationIndex (le_sup_right : A ≤ Z ⊔ A) w * m w =
          mA (w.comap (ringMap le_sup_right))) := by
  set L := Z ⊔ A
  have hBL : B ≤ L := hBZ.trans le_sup_left
  letI : FiniteDimensional (rationalBase k t) L := IntermediateField.finiteDimensional_sup Z A
  letI : CharZero (rationalBase k t) :=
    charZero_of_injective_algebraMap (algebraMap k (rationalBase k t)).injective
  let N := IntermediateField.normalClosure (rationalBase k t) L Ω
  have hLN : L ≤ N := IntermediateField.le_normalClosure L
  letI : IsGalois (rationalBase k t) N := by
    letI : Algebra.IsSeparable (rationalBase k t) N :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact IsGalois.mk
  let eL (w : Ideal (coordRing t L)) : ℕ := ramificationIndex hBL w
  have hDiv (w : Ideal (coordRing t L)) (hw : w.IsMaximal) :
      eL w ∣ mB (w.comap (ringMap hBL)) := by
    obtain ⟨P, hP, hPw⟩ := normalization_exists_maximal_over hLN w hw
    subst w
    letI : P.IsMaximal := hP
    have hP0 : P ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField hP (notFieldRing t ht N)
    have hZN : Z ≤ N := le_sup_left.trans hLN
    have hAN : A ≤ N := le_sup_right.trans hLN
    have h₁ := hZ _ (normalization_comap_isMaximal hZN P hP)
    have h₂ := hA _ (normalization_comap_isMaximal hAN P hP)
    have hc₁ : (P.comap (ringMap hZN)).comap (ringMap hBZ) =
        (P.comap (ringMap hLN)).comap (ringMap hBL) := rfl
    have hc₂ : (P.comap (ringMap hAN)).comap (ringMap hBA) =
        (P.comap (ringMap hLN)).comap (ringMap hBL) := rfl
    rw [hc₁] at h₁
    rw [hc₂] at h₂
    exact ramificationIdx_sup_dvd ht hBZ hBA hZN hAN P hP0 (Dvd.intro _ h₁) (Dvd.intro _ h₂)
  have hProjection {F : IntermediateField (rationalBase k t) Ω}
      [FiniteDimensional (rationalBase k t) F] (hBF : B ≤ F) (hFL : F ≤ L)
      (mF : Ideal (coordRing t F) → ℕ)
      (hF : ∀ w : Ideal (coordRing t F), w.IsMaximal →
        ramificationIndex hBF w * mF w = mB (w.comap (ringMap hBF)))
      (w : Ideal (coordRing t L)) (hw : w.IsMaximal) :
      ramificationIndex hFL w * (mB (w.comap (ringMap hBL)) / eL w) =
        mF (w.comap (ringMap hFL)) := by
    letI : Algebra.IsSeparable (rationalBase k t) F :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    have hF' := hF _ (normalization_comap_isMaximal hFL w hw)
    have hComap : (w.comap (ringMap hFL)).comap (ringMap hBF) = w.comap (ringMap hBL) := rfl
    rw [hComap] at hF'
    have hTower : eL w =
        ramificationIndex hBF (w.comap (ringMap hFL)) * ramificationIndex hFL w :=
      ramificationIndex_tower ht hBF hFL w
    have hDvd := hDiv w hw
    rw [hTower] at hDvd ⊢
    exact pullbackMultiplicity_mul hF'
      (mB_pos _ (normalization_comap_isMaximal hBL w hw)) hDvd
  refine ⟨fun w => mB (w.comap (ringMap hBL)) / eL w, ?_, ?_,
    hProjection hBZ le_sup_left mZ hZ, hProjection hBA le_sup_right mA hA⟩
  · intro w hw
    have hDvd := hDiv w hw
    have hPos := mB_pos _ (normalization_comap_isMaximal hBL w hw)
    have hEPos : 0 < eL w := Nat.pos_of_ne_zero fun h => by
      rw [h, zero_dvd_iff] at hDvd
      exact (Nat.ne_of_gt hPos) hDvd
    exact Nat.div_pos (Nat.le_of_dvd hPos hDvd) hEPos
  · letI := ringMapAlgebra hBL
    letI : Algebra.IsIntegral (coordRing t B) (coordRing t L) := ⟨ringMap_isIntegral hBL⟩
    letI : Module.IsTorsionFree (coordRing t B) (coordRing t L) := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]
      exact ringMap_injective hBL
    letI : Algebra.IsSeparable (rationalBase k t) L :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    letI := dedekindRing t ht L
    refine (mB_fin.biUnion (t := fun v => v.primesOver (coordRing t L)) fun v hv => ?_).subset ?_
    · haveI := hv.1
      exact IsDedekindDomain.primesOver_finite v (coordRing t L)
    · rintro w ⟨hw, hne⟩
      refine Set.mem_biUnion (x := w.comap (ringMap hBL))
        ⟨normalization_comap_isMaximal hBL w hw, fun h₁ => hne ?_⟩
        ⟨hw.isPrime, ⟨rfl⟩⟩
      have hDvd := hDiv w hw
      simp only [h₁, Nat.dvd_one] at hDvd ⊢
      rw [hDvd]

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
