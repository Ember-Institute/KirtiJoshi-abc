/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent minimal adaptation of CurveField/{Basic,Place,Residue,Point,
NoncriticalBasic}.lean at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
The Fermat presentation is new and fixed by explicit equations and degree.
No existence or regularity theorem is silently installed as an instance.
-/
import Definitions.Def_TripodFermatInputs
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Data.Finsupp.Basic
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

set_option autoImplicit false

open scoped IntermediateField WithZero

namespace AbcAdaptation.Tripod.Fermat.Proper

abbrev Ω : Type := AlgebraicClosure (RatFunc ℚ)

/-- An actual presentation of the Fermat function field. The degree-N condition
rules out a proper factor of V^N−(1−U^N); transcendence and generation rule out
an algebraic or larger unrelated field. Existence is a separate open node. -/
structure Model (N : ℕ) where
  K : IntermediateField ℚ Ω
  u : K
  v : K
  transcendental_u : Transcendental ℚ u
  equation : u ^ N + v ^ N = 1
  generate : ℚ⟮u, v⟯ = ⊤
  finite_u : FiniteDimensional ℚ⟮u⟯ K
  degree_u : Module.finrank ℚ⟮u⟯ K = N

/-- Transcendence degree one follows from the explicit presentation;
it is not another assumed structural field. -/
theorem Model.trdeg_eq_one {N : ℕ} (M : Model N) : Algebra.trdeg ℚ M.K = 1 := by
  letI : FiniteDimensional ℚ⟮M.u⟯ M.K := M.finite_u
  have ht : IsTranscendenceBasis ℚ (fun _ : Unit => M.u) := by
    refine (algebraicIndependent_unique_type_iff.mpr M.transcendental_u).isTranscendenceBasis_iff_isAlgebraic.mpr ?_
    rw [Set.range_const, ← IntermediateField.isAlgebraic_adjoin_iff_top]
    infer_instance
  have := ht.lift_cardinalMk_eq_trdeg
  simpa using this.symm

/-- The actual valuative closed-point carrier of a curve function field.
No affine chart is selected, so places at infinity are included. -/
abbrev Place (K : Type*) [Field K] : Type _ :=
  {O : ValuationSubring K // O ≠ ⊤ ∧ ∀ q : ℚ, (q : K) ∈ O}

namespace Place

variable {K : Type*} [Field K] [CharZero K]

abbrev ResidueField (P : Place K) : Type _ := IsLocalRing.ResidueField P.1

noncomputable def residue (P : Place K) : P.1 →+* P.ResidueField :=
  IsLocalRing.residue P.1

noncomputable def ratHom (P : Place K) : ℚ →+* P.1 :=
  (Rat.castHom K).codRestrict P.1 P.2.2

instance (P : Place K) : CharZero P.ResidueField :=
  charZero_of_injective_ringHom (P.residue.comp P.ratHom).injective

noncomputable def degree (P : Place K) : ℕ :=
  Module.finrank ℚ P.ResidueField

end Place

/-- A genuine algebraic point on the regular proper model, including its
residue-field embedding into the fixed algebraic closure of ℚ. -/
structure QbarPoint (K : Type*) [Field K] [CharZero K] where
  P : Place K
  σ : P.ResidueField →+* Qbar

namespace QbarPoint

variable {K : Type*} [Field K] [CharZero K]

noncomputable def eval (x : QbarPoint K) (f : K) (hf : f ∈ x.P.1) : Qbar :=
  x.σ (x.P.residue ⟨f, hf⟩)

noncomputable def fieldOf (x : QbarPoint K) : IntermediateField ℚ Qbar :=
  x.σ.toRatAlgHom.fieldRange

noncomputable def degree (x : QbarPoint K) : ℕ :=
  Module.finrank ℚ x.fieldOf

theorem eval_mem_fieldOf (x : QbarPoint K) (f : K) (hf : f ∈ x.P.1) :
    x.eval f hf ∈ x.fieldOf :=
  ⟨x.P.residue ⟨f, hf⟩, rfl⟩

end QbarPoint

variable {N : ℕ}

/-- Precise regularity obligation, independently supplied. The type makes no
choice of valuation or ramification law. -/
def PlacesDiscrete (M : Model N) : Prop :=
  ∀ P : Place M.K, IsDiscreteValuationRing P.1

/-- Precise residue-field finiteness obligation, independently supplied. -/
def ResiduesFinite (M : Model N) : Prop :=
  ∀ P : Place M.K, FiniteDimensional ℚ P.ResidueField

/-- The source's normalized discrete order, parameterized by the explicit
regularity theorem. This is not an arbitrary order-valued function. -/
noncomputable def ord (M : Model N) (hDVR : PlacesDiscrete M)
    (P : Place M.K) (f : M.K) : ℤ := by
  letI : IsDiscreteValuationRing P.1 := hDVR P
  exact -WithZero.log (((IsDiscreteValuationRing.maximalIdeal P.1).valuation M.K) f)

/-- Actual cusps, at zeros, poles, or value one, including places at infinity. -/
def cusps (M : Model N) (hDVR : PlacesDiscrete M) (φ : M.K) : Set (Place M.K) :=
  {P | ord M hDVR P φ ≠ 0 ∨ 0 < ord M hDVR P (φ - 1)}

/-- The ramification index computed by the minimal polynomial of the residue,
or minus the pole order. Residue finiteness makes this the geometric index. -/
noncomputable def ramIdx (M : Model N) (hDVR : PlacesDiscrete M)
    (φ : M.K) (P : Place M.K) : ℤ := by
  classical
  exact if h : φ ∈ P.1 then
    ord M hDVR P (Polynomial.aeval φ (minpoly ℚ (P.residue ⟨φ, h⟩)))
  else -ord M hDVR P φ

/-- A true Belyi condition on all valuative places, not an affine derivative
surrogate. The residue-finite proof is separately exposed in the consumer. -/
def IsBelyi (M : Model N) (hDVR : PlacesDiscrete M) (φ : M.K) : Prop :=
  Transcendental ℚ φ ∧
    ∀ P : Place M.K, 1 < ramIdx M hDVR φ P → P ∈ cusps M hDVR φ

/-- Genuine divisors on all proper valuative places. -/
abbrev Divisor (M : Model N) : Type := Place M.K →₀ ℤ

noncomputable def divisorDegree (M : Model N) (D : Divisor M) : ℤ :=
  D.sum fun P n => n * (P.degree : ℤ)

/-- The reduced cusp divisor, parameterized only by a proof of its actual
finite support. No height function or divisor coefficient is freely supplied. -/
noncomputable def cuspDivisor (M : Model N) (hDVR : PlacesDiscrete M) (φ : M.K)
    (hfin : (cusps M hDVR φ).Finite) : Divisor M :=
  ∑ P ∈ hfin.toFinset, Finsupp.single P 1

/-- The canonical degree of the smooth degree-N plane Fermat curve. Its
identification with the valuative canonical divisor is a later explicit node. -/
def planeCanonicalDegree (N : ℕ) : ℤ := (N : ℤ) * ((N : ℤ) - 3)

/-- The strict quantitative condition needed by the height-comparison child.
This records the actual degree of the reduced cusp divisor. No equality at
the degree ratio is accepted. -/
def StrictQ (M : Model N) (hDVR : PlacesDiscrete M) (φ : M.K)
    (hfin : (cusps M hDVR φ).Finite) (q : ℝ) : Prop :=
  (divisorDegree M (cuspDivisor M hDVR φ hfin) : ℝ) /
    (planeCanonicalDegree N : ℝ) < q

/-- The affine open corresponding to the already fixed point carrier. -/
def AffinePoint (M : Model N) : Type :=
  {x : QbarPoint M.K // ∃ (hu : M.u ∈ x.P.1) (hv : M.v ∈ x.P.1),
    x.eval M.u hu ≠ 0 ∧ x.eval M.v hv ≠ 0}

/-- Exact identity of the affine valuative model with the existing Fermat
algebraic pairs, including the actual point field. Its existence is open. -/
structure AffineIdentification (M : Model N) where
  equiv : AffinePoint M ≃ AbcAdaptation.Tripod.Fermat.Pt N
  eval_u : ∀ x : AffinePoint M, ∀ hu : M.u ∈ x.1.P.1,
    (equiv x).1.1 = x.1.eval M.u hu
  eval_v : ∀ x : AffinePoint M, ∀ hv : M.v ∈ x.1.P.1,
    (equiv x).1.2 = x.1.eval M.v hv
  field_eq : ∀ x : AffinePoint M,
    x.1.fieldOf = AbcAdaptation.Tripod.Fermat.fieldOf (equiv x)

/-- Source-faithful noncritical Belyi selection on the concrete Fermat field.
This says that arbitrary finite sets of proper places avoid the cusps. -/
def NoncriticalSelection (M : Model N) (hDVR : PlacesDiscrete M) : Prop :=
  ∀ T : Finset (Place M.K), ∃ φ : M.K,
    IsBelyi M hDVR φ ∧ ∀ P ∈ T, P ∉ cusps M hDVR φ

/-- The exact next geometric input. Every existential component has a
separate open theorem below; no assertion is installed in Definitions. -/
def NoncriticalInput (N : ℕ) : Prop :=
  ∃ M : Model N, ∃ hDVR : PlacesDiscrete M,
    ResiduesFinite M ∧ Nonempty (AffineIdentification M) ∧
      NoncriticalSelection M hDVR ∧
      (∀ φ : M.K, IsBelyi M hDVR φ → (cusps M hDVR φ).Finite)

end AbcAdaptation.Tripod.Fermat.Proper
