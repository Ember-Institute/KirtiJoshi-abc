/- Adaptation draft: the complete original Corollary22Inputs, ThetaDataExistence, and threshold commands. The original numeric definitions are imported from their separate package. Original field types and bodies are unchanged; no Open theorem supplies a field. Original source notice retained. -/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Corollary22_NumericInputs
import Definitions.Def_AbcAdaptation_Reference_Genl_GeneralPosition_HeightTheory
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Invariants
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_LogVolumeBound
import Definitions.Def_AbcAdaptation_Reference_Genl_Mathlib_Order_BoundedDiscrepancy
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Data.Finite.Defs

namespace AbcAdaptation.Reference


set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

namespace Iut

universe u v w

open Finset Real

variable (T : Genl.HeightTheory)

/-- **The standard height-theoretic inputs of Corollary 2.2** for a compactly bounded
subset `K` of the tripod and a degree bound `d`: the function `log(q_∀)`, the local height
data of each curve over its Θ-data field `F` (with `[F : ℚ] ≤ δ`), Corollary 2.2(i),
Northcott finiteness, the bound of the contribution of the prime `2`, [GenEll] Lemma 3.5
and Lemma 3.1(iii), and the four exceptional `j`-invariants of [CanLift], Proposition 2.7.
All are standard arithmetic geometry or absolute anabelian geometry, delegated to the
sibling projects (taxis #1452, #10). -/
structure Corollary22Inputs (K : T.CBS) (d : ℕ) where
  /-- The height `h = log(q_∀(−))`: the normalized degree of the `q`-divisor at all
  nonarchimedean primes. -/
  h : T.Pt T.tripod → ℝ
  /-- The local height data of the elliptic curve of `x` over its Θ-data field `F`. -/
  localData : ∀ x : T.Pt T.tripod, x ∈ T.cbsSet K ∩ T.ptLE T.tripod d → LocalHeightData.{w}
  /-- The local height data computes `h`. -/
  localData_height : ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d),
    (localData x hx).height = h x
  /-- `[F : ℚ] ≤ δ = 2¹²·3³·5·d` ((E3)–(E5) in the proof of Theorem 1.10). -/
  localData_deg_le : ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d),
    (localData x hx).deg ≤ 552960 * d
  /-- **Corollary 2.2(i)**: `(1/6)·log(q_∀) ≈ ht_{ω_X(D)}` on `K_V` ([GenEll],
  Proposition 1.4(i),(iii), Lemma 3.7, and `(∗j-inv)`). -/
  htCan_equiv : ((1 / 6 : ℝ) • h) ≈[T.cbsSet K] T.htCan T.tripod
  /-- **Northcott finiteness** ([GenEll], Proposition 1.4(iv) with (i)): finitely many
  points of `K_V ∩ U_X(ℚ̄)^{≤d}` of bounded height. -/
  northcott : ∀ H : ℝ, {x | x ∈ T.cbsSet K ∩ T.ptLE T.tripod d ∧ h x ≤ H}.Finite
  /-- The bound `B_K` on the contribution of the prime `2` to `log(q_∀)`, from
  `(∗j-inv)`. -/
  B : ℝ
  /-- `B_K ≥ 0`. -/
  B_nonneg : 0 ≤ B
  /-- The contribution of the places over `2` is bounded on `K_V`. -/
  heightEq_two_le : ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d),
    (localData x hx).heightEq 2 ≤ B
  /-- `E_x` has an `ℓ`-cyclic subgroup scheme (in the terminology of [GenEll],
  Lemma 3.5). -/
  HasCyclicSubgroup : T.Pt T.tripod → ℕ → Prop
  /-- The number `T_K` of [GenEll], Lemma 3.5 (with `ε = 1`). -/
  TK : ℝ
  /-- **[GenEll], Lemma 3.5 with Proposition 3.4, away from `2`**: an `ℓ`-cyclic subgroup scheme
  forces `((ℓ−2)/24)·(log(q_∀) − log(q₂)) ≤ 2·log ℓ + T_K`, where `log(q₂)` is the part of
  `log(q_∀)` supported over `2` (bounded by `B_K`). This is all that the proof of (P4) uses:
  the contribution of the prime `2` is absorbed into the threshold. -/
  cyclic_bound : ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d),
    ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ →
    (∀ w ∈ (localData x hx).bad, ¬ ℓ ∣ (localData x hx).hv w) →
    HasCyclicSubgroup x ℓ →
    ((ℓ : ℝ) - 2) / 24 * (h x - (localData x hx).heightEq 2) ≤ 2 * Real.log ℓ + TK
  /-- The image of `Gal(ℚ̄/F) → GL₂(𝔽_ℓ)` on the `ℓ`-torsion of `E_x` contains
  `SL₂(𝔽_ℓ)`. -/
  SL2Image : T.Pt T.tripod → ℕ → Prop
  /-- **[GenEll], Lemma 3.1(iii)**: (P2), (P4) and (P5) imply (P6). -/
  sl2_of : ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d),
    ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ →
    (∀ v ∈ (localData x hx).bad, ¬ ℓ ∣ (localData x hx).hv v) →
    ¬ HasCyclicSubgroup x ℓ →
    (∃ v ∈ (localData x hx).bad, (localData x hx).p v ≠ 2 ∧ (localData x hx).p v ≠ ℓ) →
    SL2Image x ℓ
  /-- The points whose once-punctured elliptic curve fails to have an `F`-core
  ([CanLift], Proposition 2.7: four `j`-invariants; taxis #10). -/
  excCore : Set (T.Pt T.tripod)
  /-- Finitely many such points of bounded degree. -/
  excCore_finite : (excCore ∩ (T.cbsSet K ∩ T.ptLE T.tripod d)).Finite

variable {T}

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- **Existence of suitable initial Θ-data** ((P7) in the proof of Corollary 2.2): for a
point `x` outside the exceptional set and a prime `ℓ ≥ 7` satisfying (P2), (P3), (P5),
(P6), there are initial Θ-data with prime `ℓ` in the situation of Theorem 1.10 — i.e.
a Corollary 3.12 variant data bundle with its Theorem 1.10 invariants, certificate and
local estimates — whose `log(q)` is the part of `log(q_∀)` away from `2` and `ℓ`, with
`d_mod ≤ d`, and whose different and conductor invariants match `log-diff_X(x)` and
`log-cond_D(x)` (the equality and the two inequalities recorded at the end of the proof of
Corollary 2.2). The predicate `P` restricts the data bundles produced (e.g. to the concrete
ones of `Iut.concreteVariantData`); the Corollary 3.12 variant is only assumed on them.

This is the IUT-theoretic input of Corollary 2.2 (IUT I, Definition 3.1(d)–(f); *The
Étale Theta Function*, Definitions 2.1–2.5): the construction of `C̲_K`, `V`, `ε` from
the `SL₂` image. It is an open obligation of this repository, blocked on the anabelian
interfaces (taxis #276, #279). -/
structure ThetaDataExistence (P : Corollary312VariantData.{u, v} AG TG → Prop)
    {K : T.CBS} {d : ℕ} (I : Corollary22Inputs T K d) : Prop where
  thetaData : ∀ x (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d), x ∉ I.excCore →
    ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ →
    (∀ v ∈ (I.localData x hx).bad, ¬ ℓ ∣ (I.localData x hx).hv v) →
    (∀ v ∈ (I.localData x hx).bad, (I.localData x hx).p v = ℓ →
      ((I.localData x hx).hv v : ℝ) < Real.sqrt (I.h x)) →
    (∃ v ∈ (I.localData x hx).bad, (I.localData x hx).p v ≠ 2 ∧ (I.localData x hx).p v ≠ ℓ) →
    I.SL2Image x ℓ →
    ∃ (X : Corollary312VariantData.{u, v} AG TG) (inv : Theorem110Invariants X), P X ∧
      Theorem110Certificate inv ∧ Nonempty inv.LocalEstimate ∧ X.ℓ = ℓ ∧ X.dmod ≤ d ∧
      X.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ ∧
      T.logDiff T.tripod x = inv.logDtpd ∧
      inv.logFtpd ≤ T.logCond T.tripod x ∧
      T.logCond T.tripod x ≤ inv.logFtpd + Real.log (2 * ℓ)

namespace Corollary22Inputs

variable {K : T.CBS} {d : ℕ} (I : Corollary22Inputs T K d)

/-- The threshold above which (P4), (P5), `√h ≥ ξ_prm` and `ε_E ≤ 1` all hold. -/
noncomputable def threshold (cheb : ChebyshevBound) : ℝ :=
  max (max (cheb.ξ ^ 2) (49 + 8 * max I.TK 0 + I.B))
    (max ((I.B + 11 + 2 * deltaBound d) ^ 4 + 1)
      (((60 * deltaBound d) ^ 2 * (2 * deltaBound d + 4)) ^ 4 + 1))

end Corollary22Inputs

attribute [local congr] Corollary22Inputs.localData.congr_simp

end Iut

end AbcAdaptation.Reference
