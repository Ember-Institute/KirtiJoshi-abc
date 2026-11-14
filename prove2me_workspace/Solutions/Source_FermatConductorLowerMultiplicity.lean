/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source adaptation. Pinned proofs and consumer mappings: SOURCE_LEDGER.md.
-/
import Definitions.Def_FermatBelyiConductorExtensionFinitePlaces

set_option autoImplicit false
open NumberField IsDedekindDomain Module

namespace AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Multiplicity

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

lemma finiteMultiplicity_of_isPrime {P I : Ideal R} [P.IsPrime] (hP : P ≠ ⊥) (hI : I ≠ ⊥) :
    FiniteMultiplicity P I :=
  FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hP inferInstance) hI

/-- `P^n ∣ I ↔ n ≤ ord_P(I)` for a nonzero prime `P` and `I ≠ 0`. -/
lemma pow_dvd_iff_le_multiplicity {P I : Ideal R} [P.IsPrime] (hP : P ≠ ⊥) (hI : I ≠ ⊥)
    {n : ℕ} : P ^ n ∣ I ↔ n ≤ multiplicity P I :=
  (finiteMultiplicity_of_isPrime hP hI).pow_dvd_iff_le_multiplicity

end Multiplicity

section Prime

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsMaximal] (h𝔭 : 𝔭 ≠ ⊥) (P : Ideal (𝓞 L)) [P.IsPrime]
  [P.LiesOver 𝔭]

include h𝔭

omit [NumberField F] [NumberField L] [𝔭.IsMaximal] [P.IsPrime] in
lemma ne_bot_of_liesOver : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 P

omit [P.IsPrime] in
/-- `log N(P) = f(P|𝔭)·log N(𝔭)`. -/
lemma log_absNorm_eq_inertiaDeg_mul :
    Real.log (Ideal.absNorm P) = 𝔭.inertiaDeg' P * Real.log (Ideal.absNorm 𝔭) := by
  rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P 𝔭 inferInstance h𝔭, Nat.cast_pow,
    Real.log_pow]

omit h𝔭 [NumberField F] [𝔭.IsMaximal] [P.IsPrime] [P.LiesOver 𝔭] in
lemma pow_ramificationIdx'_dvd :
    P ^ 𝔭.ramificationIdx' P ∣ 𝔭.map (algebraMap (𝓞 F) (𝓞 L)) :=
  Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx'

/-- **(a)** `e(P|𝔭) − 1 ≤ ord_P(𝔇)`. -/
lemma ramificationIdx'_sub_one_le_multiplicity :
    𝔭.ramificationIdx' P - 1 ≤ multiplicity P (differentIdeal (𝓞 F) (𝓞 L)) :=
  (pow_dvd_iff_le_multiplicity (ne_bot_of_liesOver h𝔭 P) differentIdeal_ne_bot).mp
    (pow_sub_one_dvd_differentIdeal (𝓞 F) P _ h𝔭 (pow_ramificationIdx'_dvd P))

end Prime

end AbcAdaptation.Tripod.Fermat.Proper.ConductorExtensionSource
