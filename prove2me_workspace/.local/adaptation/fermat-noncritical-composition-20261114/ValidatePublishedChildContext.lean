import Definitions.Def_FermatNoncriticalRamificationPositive

set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- OPEN: the actual single-elementary-map composition step from the source.
The map is a rational Möbius transformation with nonzero determinant or a
positive-degree rational polynomial. Every actual residue embedding is kept. -/
theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalElementaryCompositionRamification {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (x : QbarPoint M.K) (h : NoncriticalP1.ElemMap) :
    Transcendental ℚ (NoncriticalP1.applyK h ψ) ∧
    noncriticalValue M x (NoncriticalP1.applyK h ψ) = h.apply (noncriticalValue M x ψ) ∧
    ramIdx M hDVR (NoncriticalP1.applyK h ψ) x.P =
      ramIdx M hDVR ψ x.P * (h.ramIdx (noncriticalValue M x ψ) : ℤ) := by
  sorry


set_option autoImplicit false
open scoped IntermediateField
open AbcAdaptation.Tripod.Fermat.Proper

/-- Positivity and the source list induction for actual rational elementary
composites, preserving the exact existing all-points target statement. -/
theorem solution {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ) :
    (∀ P : Place M.K, 0 < ramIdx M hDVR ψ P) ∧
    ∀ (hs : List NoncriticalP1.ElemMap) (x : QbarPoint M.K),
      Transcendental ℚ (NoncriticalP1.compK hs ψ) ∧
      noncriticalValue M x (NoncriticalP1.compK hs ψ) =
        NoncriticalP1.evalComp hs (noncriticalValue M x ψ) ∧
      ramIdx M hDVR (NoncriticalP1.compK hs ψ) x.P =
        ramIdx M hDVR ψ x.P *
          (NoncriticalP1.ramIdxComp hs (noncriticalValue M x ψ) : ℤ) := by
  refine ⟨noncriticalRamificationPositive M hDVR ψ hψ, ?_⟩
  intro hs x
  induction hs generalizing ψ with
  | nil =>
    exact ⟨hψ, rfl, by simp [NoncriticalP1.compK, NoncriticalP1.ramIdxComp]⟩
  | cons h hs ih =>
    obtain ⟨h1, h2, h3⟩ :=
      noncriticalElementaryCompositionRamification M hDVR ψ hψ x h
    obtain ⟨i1, i2, i3⟩ := ih (ψ := NoncriticalP1.applyK h ψ) h1
    refine ⟨i1, ?_, ?_⟩
    · change noncriticalValue M x (NoncriticalP1.compK hs (NoncriticalP1.applyK h ψ)) = _
      rw [i2, h2]
      rfl
    · change ramIdx M hDVR (NoncriticalP1.compK hs (NoncriticalP1.applyK h ψ)) x.P = _
      rw [i3, h3, h2]
      simp only [NoncriticalP1.ramIdxComp, Nat.cast_mul, mul_assoc]

#print axioms solution
