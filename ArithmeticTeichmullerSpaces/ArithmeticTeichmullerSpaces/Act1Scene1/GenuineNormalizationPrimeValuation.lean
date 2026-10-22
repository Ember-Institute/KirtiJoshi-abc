/-
original-path: `refer/iut/Iut/Anabelian/Genuine/Homs.lean`
original-author: Christian Merten <lana@merten.dev> (Git author)
original-file-authors: The iut contributors
original-coauthor: Claude Opus 5.5 (1M context) <noreply@anthropic.com> (Git trailer)
original-commit: `b51b94cad5c729f753ed0790b5fb95d9d65aaff1`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the source copyright and Apache-2.0 license before
copying. No NOTICE file occurs in the reference tree. Retain the notice below.
modifications: separate the valuation comparison from the division-point proof.
Use Mathlib's actual integral-closure action and Ideal.inertia. Use valuation
equivalence for the prime-membership comparison. Keep default proof budgets.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.NormalizationPrimeValuation
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.Normalization
import Mathlib.RingTheory.Ideal.Pointwise

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Genuine/Homs.lean, the valuation at a nonzero normalization prime.
fidelity: actual automorphisms of a finite extension act on its actual integral
closure. Membership in a prime's actual inertia gives the valuation inequality
used in the division-point inertia theorem.
boundary: Scene1/Derived. No covering or ramification-index law is assumed.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve JoshiTeich.Act1Scene1
open scoped Classical IntermediateField.algebraAdjoinAdjoin Pointwise
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]
variable (N : IntermediateField (xLine E) (Ω E))

local instance primeNormalizationSeparable : Algebra.IsSeparable (xLine E) N := by
  have : CharZero (xLine E) := charZero_of_injective_algebraMap (algebraMap k (xLine E)).injective
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- The same normalization, with its coefficient field exposed as k. -/
abbrev normalizationCoeffSubalgebra : Subalgebra k N :=
  (FunctionFieldNormalization.coordRing (xG E) N).restrictScalars k

omit [CharZero k] [E.IsElliptic] in
theorem normalizationCoeffSubalgebra_integrallyClosed (x : N)
    (hx : IsIntegral (normalizationCoeffSubalgebra E N) x) :
    x ∈ normalizationCoeffSubalgebra E N :=
  isIntegral_trans (R := Algebra.adjoin k {xG E})
    (A := FunctionFieldNormalization.coordRing (xG E) N) x hx

local instance primeNormalizationCoeffComm :
    SMulCommClass (N ≃ₐ[xLine E] N) (Algebra.adjoin k {xG E}) N where
  smul_comm τ a b := by
    change τ (algebraMap (Algebra.adjoin k {xG E}) N a * b) =
      algebraMap (Algebra.adjoin k {xG E}) N a * τ b
    rw [map_mul, show τ (algebraMap (Algebra.adjoin k {xG E}) N a) =
      algebraMap (Algebra.adjoin k {xG E}) N a from
        τ.commutes (algebraMap (Algebra.adjoin k {xG E}) (xLine E) a)]

/-- Restrict the actual field automorphisms to the actual integral closure. -/
@[instance_reducible] def normalizationFieldRingAction :
    MulSemiringAction (N ≃ₐ[xLine E] N) (FunctionFieldNormalization.coordRing (xG E) N) :=
  inferInstance

attribute [local instance] normalizationFieldRingAction

omit [CharZero k] [E.IsElliptic] in
@[simp] theorem coe_normalizationFieldRingAction (τ : N ≃ₐ[xLine E] N)
    (a : FunctionFieldNormalization.coordRing (xG E) N) :
    ((τ • a : FunctionFieldNormalization.coordRing (xG E) N) : N) = τ (a : N) := rfl

variable [FiniteDimensional (xLine E) N]

local instance primeNormalizationDedekind :
    IsDedekindDomain (FunctionFieldNormalization.coordRing (xG E) N) :=
  FunctionFieldNormalization.dedekindRing (xG E) (transcendental_xG E) N

local instance primeNormalizationFraction :
    IsFractionRing (FunctionFieldNormalization.coordRing (xG E) N) N :=
  FunctionFieldNormalization.fractionFieldRing (xG E) N

/-- The actual valuation subring at a nonzero prime of the normalization. -/
def normalizationPrimeSubring
    (p : IsDedekindDomain.HeightOneSpectrum (FunctionFieldNormalization.coordRing (xG E) N)) :
    ValuationSubring N := NormalizationPrimeValuation.primeSubring N p

theorem normalization_mem_primeSubring
    (p : IsDedekindDomain.HeightOneSpectrum (FunctionFieldNormalization.coordRing (xG E) N))
    (a : FunctionFieldNormalization.coordRing (xG E) N) :
    (a : N) ∈ normalizationPrimeSubring E N p :=
  NormalizationPrimeValuation.coordinate_mem p a

theorem normalizationPrime_inertia_lt_one
    (p : IsDedekindDomain.HeightOneSpectrum (FunctionFieldNormalization.coordRing (xG E) N))
    (τ : N ≃ₐ[xLine E] N) (hτ : τ ∈ p.asIdeal.inertia (N ≃ₐ[xLine E] N))
    (a : FunctionFieldNormalization.coordRing (xG E) N) :
    (normalizationPrimeSubring E N p).valuation (τ (a : N) - (a : N)) < 1 :=
  (NormalizationPrimeValuation.valuation_lt_one_iff_mem p (τ • a - a)).mpr
    ((Ideal.mem_inertia).mp hτ a)

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
