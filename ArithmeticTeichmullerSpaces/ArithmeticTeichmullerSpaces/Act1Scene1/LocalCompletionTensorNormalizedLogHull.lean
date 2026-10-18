import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorEqualNormHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorPointOrbitHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerNormalizedIntegralLog
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-NORMALIZED-LOG-HULL
source: Joshi III eq:bloch-kato-log-class, le:elem-lemma and the
standard-point witness in th:moccor-Mochizuki-form2.
fidelity: actual principal integral Kummer images over each completion's
algebraic closure have normalized ordinary log log(1+pStar*y)/pStar.
For integral nonzero factor scalars, their tensor singleton hull and
factor-orbit hull equal those of the original scalars, by equal norms.
Original proofs; no reference source code copied.
boundary: Scene1/Derived; no H1e/BK or different-untilt identification.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open NumberField
open scoped Classical Valued
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance logHullFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance logHullFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance logHullFactorContinuousSMul (i : ι) : ContinuousSMul ℚ_[p] (P.Factor i) :=
  continuousSMul_of_algebraMap ℚ_[p] _ (continuous_padicEmb (P.residueChar_eq i))
local instance logHullFactorCharZero (i : ι) : CharZero (P.Factor i) :=
  charZero_of_injective_ringHom (FinitePlace.embedding (P.place i).maximalIdeal).injective
local instance logHullIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

omit [Fact p.Prime] [Fintype ι] in
theorem logHull_norm_prime_lt_one (i : ι) : ‖(p : P.Factor i)‖ < 1 := by
  have h := norm_natCast_prime_lt_one (P.residueChar_eq i)
  rwa [← FinitePlace.embedding_apply, map_natCast] at h

def paperLogScalars (z : ∀ i, P.Factor i) : ∀ i, P.Factor i :=
  fun i => LocalPadicLog.paperNormalizedLog p (z i)

omit [Fintype ι] in
theorem paperLogScalars_norm (z : ∀ i, P.Factor i) (hz1 : ∀ i, ‖z i‖ ≤ 1) (i : ι) :
    ‖P.paperLogScalars z i‖ = ‖z i‖ :=
  LocalPadicLog.norm_paperNormalizedLog (Fact.out : p.Prime)
    (P.logHull_norm_prime_lt_one i) (hz1 i)

omit [Fintype ι] in
theorem paperLogScalars_ne_zero (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)
    (hz1 : ∀ i, ‖z i‖ ≤ 1) (i : ι) : P.paperLogScalars z i ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [P.paperLogScalars_norm z hz1]
  exact norm_ne_zero_iff.mpr (hz i)

def paperLogPrincipalUnit (z : ∀ i, P.Factor i) (hz1 : ∀ i, ‖z i‖ ≤ 1) (i : ι) :
    LocalPadicLog.principalUnits (k := P.Factor i) :=
  ⟨Units.mk0 (LocalPadicLog.paperPrincipalUnit p (z i))
    (LocalPadicLog.paperPrincipalUnit_ne_zero (Fact.out : p.Prime)
      (P.logHull_norm_prime_lt_one i) (hz1 i)),
    LocalPadicLog.paperPrincipalUnit_norm_sub_one_lt_one (Fact.out : p.Prime)
      (P.logHull_norm_prime_lt_one i) (hz1 i)⟩

def paperLogIntegralClass (z : ∀ i, P.Factor i) (hz1 : ∀ i, ‖z i‖ ≤ 1) (i : ι) :
    LocalPadicLog.integralKummerSubmodule (Ω := AlgebraicClosure (P.Factor i)) p
      (P.logHull_norm_prime_lt_one i) :=
  LocalPadicLog.principalIntegralClass p (P.logHull_norm_prime_lt_one i)
    (Additive.ofMul (P.paperLogPrincipalUnit z hz1 i))

omit [Fintype ι] in
theorem paperLogIntegralClass_normalizedLog (z : ∀ i, P.Factor i)
    (hz1 : ∀ i, ‖z i‖ ≤ 1) (i : ι) :
    (LocalPadicLog.normalizedIntegralKummerLogEquiv p (P.logHull_norm_prime_lt_one i)
      (P.paperLogIntegralClass z hz1 i) : P.Factor i) = P.paperLogScalars z i :=
  LocalPadicLog.normalizedIntegralKummerLog_principal p (P.logHull_norm_prime_lt_one i)
    (Additive.ofMul (P.paperLogPrincipalUnit z hz1 i))

omit [Fintype ι] in
theorem paperLogIntegralClass_has_integralLift (z : ∀ i, P.Factor i)
    (hz1 : ∀ i, ‖z i‖ ≤ 1) (i : ι) :
    ∃ x, LocalKummer.Rational.standardMap (K := P.Factor i) (Ω := AlgebraicClosure (P.Factor i)) p x =
      (P.paperLogIntegralClass z hz1 i).1.1 :=
  (LocalPadicLog.mem_integralKummerSubmodule_iff p (P.logHull_norm_prime_lt_one i) _).mp
    (P.paperLogIntegralClass z hz1 i).2

theorem scalarNormalization_paperLogScalars (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)
    (hz1 : ∀ i, ‖z i‖ ≤ 1) :
    (P.scalarNormalization (P.paperLogScalars z) (P.paperLogScalars_ne_zero z hz hz1) : Set P.Tensor) =
      P.scalarNormalization z hz :=
  P.scalarNormalization_eq_of_norm_eq _ _ _ _ (P.paperLogScalars_norm z hz1)

theorem factorOrbitScalarRegion_paperLogScalars (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)
    (hz1 : ∀ i, ‖z i‖ ≤ 1) :
    P.factorOrbitScalarRegion (P.paperLogScalars z) (P.paperLogScalars_ne_zero z hz hz1) =
      P.factorOrbitScalarRegion z hz := by
  unfold factorOrbitScalarRegion
  rw [P.scalarNormalization_paperLogScalars z hz hz1]

theorem singletonHull_paperLogScalars (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)
    (hz1 : ∀ i, ‖z i‖ ≤ 1) :
    (P.normalizationHull {P.pure (P.paperLogScalars z)} : Set P.Tensor) =
      P.principalRegion (P.pure z) := by
  rw [P.normalizationHull_singleton_eq_principalRegion,
    ← P.scalarNormalization_eq_principalRegion _ (P.paperLogScalars_ne_zero z hz hz1),
    P.scalarNormalization_paperLogScalars z hz hz1, P.scalarNormalization_eq_principalRegion]

theorem pointOrbitHull_paperLogScalars (z : ∀ i, P.Factor i) (hz : ∀ i, z i ≠ 0)
    (hz1 : ∀ i, ‖z i‖ ≤ 1) :
    P.normalizationHull (P.factorPointOrbit (P.pure (P.paperLogScalars z))) =
      P.normalizationHull (P.factorPointOrbit (P.pure z)) := by
  rw [P.normalizationHull_factorPointOrbit, P.normalizationHull_factorPointOrbit]
  have he : P.principalRegion (P.pure (P.paperLogScalars z)) = P.principalRegion (P.pure z) := by
    rw [← P.normalizationHull_singleton_eq_principalRegion, P.singletonHull_paperLogScalars z hz hz1]
  rw [he]

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
