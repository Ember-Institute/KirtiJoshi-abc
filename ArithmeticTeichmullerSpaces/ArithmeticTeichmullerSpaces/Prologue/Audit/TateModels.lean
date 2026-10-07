import ArithmeticTeichmullerSpaces.Prologue.Audit.Models

namespace JoshiTeich.Prologue.Audit

open JoshiTeich.Prologue.Theta
open scoped NumberField

theorem auditTateData_laws : TateParameterLaws auditTateData := by
  constructor
  · simp [auditTateData]
  · intro w hw
    simpa only [auditTateData] using
      (map_ne_zero (NumberField.FinitePlace.embedding w.maximalIdeal)).2 (by norm_num)
  · intro w hw
    exact (NumberField.FinitePlace.norm_embedding_eq w (2 : ℚ)).symm
  · intro w hw
    exact NumberField.FinitePlace.pos_iff.mpr (by norm_num [auditTateData])
  · intro w hw
    simp only [auditTateData, Finset.mem_singleton] at hw ⊢
    subst w
    unfold rationalTwoPlace
    change ‖NumberField.FinitePlace.embedding rationalTwoHeightOne (2 : ℚ)‖ < 1
    have hnorm :
        ‖NumberField.FinitePlace.embedding rationalTwoHeightOne
            (algebraMap (𝓞 ℚ) ℚ (2 : 𝓞 ℚ))‖ < 1 :=
      (NumberField.FinitePlace.norm_lt_one_iff_mem ℚ rationalTwoHeightOne
        (2 : 𝓞 ℚ)).2 (by
          change (2 : 𝓞 ℚ) ∈ rationalTwoPrimeIdeal
          change Rat.ringOfIntegersEquiv (2 : 𝓞 ℚ) ∈ Ideal.span {(2 : ℤ)}
          have hmap : Rat.ringOfIntegersEquiv (2 : 𝓞 ℚ) = (2 : ℤ) := by
            apply Rat.ringOfIntegersEquiv.symm.injective
            apply NumberField.RingOfIntegers.ext
            simp [Rat.ringOfIntegersEquiv_apply_coe]
          rw [hmap]
          exact Ideal.mem_span_singleton_self _)
    have hmap : algebraMap (𝓞 ℚ) ℚ (2 : 𝓞 ℚ) = (2 : ℚ) := by
      exact map_natCast (algebraMap (𝓞 ℚ) ℚ) 2
    rw [hmap] at hnorm
    exact hnorm
  · intro w hw
    simp [auditTateData]

noncomputable def zeroTateData : TateParameterData ℚ where
  places := {rationalTwoPlace}
  parameter := fun _ => 0
  norm := fun w => w (2 : ℚ)
  orderNat := fun _ => 0

theorem auditTateData_violation : ¬ TateParameterLaws zeroTateData := by
  intro h
  have hn := h.parameter_nonzero rationalTwoPlace (by simp [zeroTateData])
  norm_num [zeroTateData] at hn

theorem auditTateData_parameter_nontrivial :
    auditTateData.parameter rationalTwoPlace =
      NumberField.FinitePlace.embedding rationalTwoPlace.maximalIdeal (2 : ℚ) := by
  rfl

end JoshiTeich.Prologue.Audit
