/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent concrete adaptation of Heights/Curve/Compactness.lean and
Genl/Curves/BelyiDescent.lean at the pinned references in source-consumer.json.
-/
import Definitions.Def_FermatProperCarrier
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Topology.Instances.Complex
import Mathlib.Order.Filter.AtTopBot.Basic

set_option autoImplicit false

open scoped IntermediateField
open Filter

namespace AbcAdaptation.Tripod.Fermat.Proper

variable {N : ℕ}

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def affineLift (M : Model N) (A : AffineIdentification M)
    (p : Fermat.Pt N) : QbarPoint M.K := (A.equiv.symm p).1

theorem affineLift_field_eq (M : Model N) (A : AffineIdentification M)
    (p : Fermat.Pt N) : (affineLift M A p).fieldOf = Fermat.fieldOf p := by
  simpa only [affineLift, Equiv.apply_symm_apply] using
    A.field_eq (A.equiv.symm p)

theorem affineLift_degree_eq (M : Model N) (A : AffineIdentification M)
    (p : Fermat.Pt N) : (affineLift M A p).degree = Fermat.degree p := by
  unfold QbarPoint.degree Fermat.degree
  rw [affineLift_field_eq]

noncomputable def evalInField (M : Model N) (x : QbarPoint M.K)
    (φ : M.K) (hφ : φ ∈ x.P.1) : x.fieldOf :=
  ⟨x.eval φ hφ, x.eval_mem_fieldOf φ hφ⟩

def GoodValue (M : Model N) (x : QbarPoint M.K) (φ : M.K) : Prop :=
  ∃ hφ : φ ∈ x.P.1, x.eval φ hφ ≠ 0 ∧ x.eval φ hφ ≠ 1

/-- Actual Belyi evaluation on its open part; the junk value 2 is used only
to make a total function and is never used on the selected failure locus. -/
noncomputable def belyiImage (M : Model N) (φ : M.K) (x : QbarPoint M.K) :
    Tripod.Pt := by
  classical
  exact if h : GoodValue M x φ then
    ⟨x.eval φ h.choose, h.choose_spec⟩
  else rationalPoint 2 (by norm_num) (by norm_num)

theorem belyiImage_eq (M : Model N) (φ : M.K) (x : QbarPoint M.K)
    (hφ : φ ∈ x.P.1) (h0 : x.eval φ hφ ≠ 0) (h1 : x.eval φ hφ ≠ 1) :
    belyiImage M φ x = ⟨x.eval φ hφ, h0, h1⟩ := by
  classical
  unfold belyiImage
  exact dif_pos ⟨hφ, h0, h1⟩

theorem belyiImage_field_le (M : Model N) (φ : M.K) (x : QbarPoint M.K)
    (hgood : GoodValue M x φ) :
    Tripod.fieldOf (belyiImage M φ x).1 ≤ x.fieldOf := by
  obtain ⟨hφ, h0, h1⟩ := hgood
  rw [belyiImage_eq M φ x hφ h0 h1]
  exact IntermediateField.adjoin_simple_le_iff.mpr (x.eval_mem_fieldOf φ hφ)

theorem belyiImage_degree_le (M : Model N) (A : AffineIdentification M)
    (φ : M.K) (p : Fermat.Pt N) (hgood : GoodValue M (affineLift M A p) φ) :
    Tripod.deg (belyiImage M φ (affineLift M A p)).1 ≤ Fermat.degree p := by
  letI : FiniteDimensional ℚ (affineLift M A p).fieldOf := by
    rw [affineLift_field_eq]
    infer_instance
  rw [Tripod.deg_eq_finrank, ← affineLift_degree_eq M A p]
  exact IntermediateField.finrank_le_of_le_right (belyiImage_field_le M φ _ hgood)

/-- Bounds at every conjugate embedding into the actual local fields. The
2-adic algebraic closure and spectral norm already exist in Mathlib. -/
def LocalBounds (M : Model N) (x : QbarPoint M.K) (φ : M.K) (c : ℝ) : Prop :=
  ∃ hφ : φ ∈ x.P.1,
    x.eval φ hφ ≠ 0 ∧ x.eval φ hφ ≠ 1 ∧
    (∀ σ : x.fieldOf →+* ℂ,
      |Real.log ‖σ (evalInField M x φ hφ)‖| ≤ c ∧
        |Real.log ‖σ (evalInField M x φ hφ) - 1‖| ≤ c) ∧
    ∀ τ : x.fieldOf →+* PadicAlgCl 2,
      |Real.log ‖τ (evalInField M x φ hφ)‖| ≤ c ∧
        |Real.log ‖τ (evalInField M x φ hφ) - 1‖| ≤ c

def LocalCompactness (M : Model N) : Prop :=
  ∀ (d : ℕ) (xs : ℕ → QbarPoint M.K), (∀ n, (xs n).degree ≤ d) →
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ T : Finset (Place M.K),
      ∀ φ : M.K, φ ≠ 0 → φ ≠ 1 →
        (∀ P ∈ T, φ ∈ P.1 ∧ φ⁻¹ ∈ P.1 ∧ (φ - 1)⁻¹ ∈ P.1) →
        ∃ c : ℝ, ∀ᶠ n in atTop, LocalBounds M (xs (s n)) φ c

def AvoidanceRegularity (M : Model N) (hDVR : PlacesDiscrete M) : Prop :=
  ∀ (φ : M.K) (P : Place M.K), P ∉ cusps M hDVR φ →
    φ ∈ P.1 ∧ φ⁻¹ ∈ P.1 ∧ (φ - 1)⁻¹ ∈ P.1

/-- A common valuation compact set for the selected images. -/
noncomputable def localCompactSet (d : ℕ) (c : ℝ) : Tripod.CompactlyBounded where
  V := {2}
  prime p hp := by
    have hp2 : p = 2 := Finset.mem_singleton.mp hp
    simpa [hp2] using Nat.prime_two
  two_mem := Finset.mem_singleton_self 2
  c := (d + 1) * max c 0

/-- Exact embedding-to-place arithmetic bridge, including degree scaling.
The same local c and degree d produce one K for every point in the sequence. -/
def EmbeddingBoundsToSet (M : Model N) : Prop :=
  ∀ (x : QbarPoint M.K) (φ : M.K) (d : ℕ) (c : ℝ),
    x.degree ≤ d → LocalBounds M x φ c →
      belyiImage M φ x ∈ (localCompactSet d c).set

/-- Actual Belyi image of every selected term, with a common compact set,
original degree bound, and explicit good evaluation at each term. -/
def BoundedBelyiImages (M : Model N) (hDVR : PlacesDiscrete M)
    (A : AffineIdentification M) : Prop :=
  ∀ (d : ℕ) (xs : ℕ → Fermat.Pt N), (∀ n, Fermat.degree (xs n) ≤ d) →
    ∃ φ : M.K, IsBelyi M hDVR φ ∧
      ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ K : Tripod.CompactlyBounded,
        ∀ n, GoodValue M (affineLift M A (xs (s n))) φ ∧
          belyiImage M φ (affineLift M A (xs (s n))) ∈ K.set ∧
          Tripod.deg (belyiImage M φ (affineLift M A (xs (s n)))).1 ≤ d

end AbcAdaptation.Tripod.Fermat.Proper
