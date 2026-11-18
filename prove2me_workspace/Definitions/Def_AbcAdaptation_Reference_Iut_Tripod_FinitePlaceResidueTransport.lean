/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision recorded by current adaptation: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Source declarations selected from the original proof; imports and namespaces adapted.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FiniteHeightMapEquiv
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_LocalHeightDataAssembly

namespace AbcAdaptation.Reference.Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section
variable {k : Type*} [Field k] [NumberField k]

lemma natCast_mem_maximalIdeal_iff (v : FinitePlace k) {q : ℕ} (hq : q.Prime) :
    (q : 𝓞 k) ∈ v.maximalIdeal.asIdeal ↔ residueChar v = q := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
    CharP.cast_eq_zero_iff (𝓞 k ⧸ v.maximalIdeal.asIdeal) (ringChar _)]
  exact Nat.prime_dvd_prime_iff_eq (residueChar_prime v) hq
end

section
variable {k k' : Type*} [Field k] [NumberField k] [Field k'] [NumberField k']
variable (e : k ≃+* k') (v : FinitePlace k)

lemma FinitePlace.mapEquiv_residueChar :
    residueChar (FinitePlace.mapEquiv e v) = residueChar v := by
  rw [← natCast_mem_maximalIdeal_iff _ (residueChar_prime v), FinitePlace.mapEquiv_maximalIdeal,
    Ideal.mem_comap, map_natCast]
  exact (natCast_mem_maximalIdeal_iff v (residueChar_prime v)).mpr rfl

end

end AbcAdaptation.Reference.Iut
