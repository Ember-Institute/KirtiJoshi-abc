/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Lean
import B1SourceReplay
import Iut.Cor312.ThetaData.Orbicurve
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
Reference replay at iut revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8.
B1SourceReplay supplies the original curve providers, Tate data, and tripodal
field identification. The copied declarations come from Concrete/Existence.lean,
Concrete/CyclicSubgroup.lean, Concrete/Invariants.lean, Tripod/CurveOf.lean,
and Tripod/CurveFacts.lean.

The section variable sl2Image is the explicit proof supplied to the replay.
Source type: CurveFacts.lean:442. Target proof and closure: ci-020827-2725d6f7.
Private platform proof: b1da5e0c-ce54-4c57-878b-200de86a8b5b.
-/

namespace Iut

universe u

open WeierstrassCurve NumberField

namespace EllipticCurveData

variable (C : EllipticCurveData.{u})

def VBadOf (ℓ : ℕ) : Set (FinitePlace ↥(fieldOfModuli C.F C.E)) :=
  {v | residueChar v ≠ 2 ∧ residueChar v ≠ ℓ ∧
    (∃ w : FinitePlace C.F, FinitePlace.LiesOver w v) ∧
    ∀ w : FinitePlace C.F, FinitePlace.LiesOver w v → HasMultiplicativeReductionAt C.E w}

open scoped Classical in
def HasCyclicSubgroup (ℓ : ℕ) : Prop :=
  ∃ H : AddSubgroup (Affine.Point (Affine.baseChange C.E C.Fbar)),
    Nat.card H = ℓ ∧ ∀ σ : C.Fbar ≃ₐ[C.F] C.Fbar, ∀ P ∈ H, galPointMap C.F C.E C.Fbar σ P ∈ H

end EllipticCurveData

noncomputable def logDifferentDeg (L : Type*) [Field L] [NumberField L] : ℝ :=
  Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 L))) / Module.finrank ℚ L

section Tripodal

variable (F : Type*) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable (VBad : Set (FinitePlace ↥(fieldOfModuli F E)))

def IsBadTpdOf (𝔭 : FinitePlace ↥(tripodalFieldOf F E)) : Prop :=
  ∃ w ∈ badPlacesOver F E VBad, (Place.finite w).LiesOver (Place.finite 𝔭)

open scoped Classical in
/-- The normalized degree `log(f_{F_tpd})` of the **conductor divisor** of `F_tpd`: the
sum of `log N(𝔭)` over the bad places of `F_tpd`, divided by `[F_tpd : ℚ]` (finitely
supported; `0` if not). -/
noncomputable def logConductorDegOf : ℝ :=
  (∑ᶠ 𝔭 : FinitePlace ↥(tripodalFieldOf F E),
    if IsBadTpdOf F E VBad 𝔭 then Real.log (Ideal.absNorm 𝔭.maximalIdeal.asIdeal) else 0) /
    Module.finrank ℚ ↥(tripodalFieldOf F E)

end Tripodal

variable (T : Genl.HeightTheory) (AG : AnabelianGeometry.{u})

structure CurveInputs (K : T.CBS) (d : ℕ) where
  /-- The height `h = log(q_∀(−))`. -/
  h : T.Pt T.tripod → ℝ
  /-- The curve `E_x/F_x` of a point. -/
  curve : ∀ x : T.Pt T.tripod, x ∈ T.cbsSet K ∩ T.ptLE T.tripod d → EllipticCurveData.{u}
  /-- The arithmetic of `E_x/F_x` (IUT IV, Proposition 1.8). -/
  arith : ∀ x hx, (curve x hx).CurveArithmetic
  /-- The Tate parameters of `E_x`. -/
  tate : ∀ x hx, (curve x hx).TateInputs
  /-- The mod-`ℓ` representations of `E_x`. -/
  modRep : ∀ x hx (ℓ : ℕ), ℓ.Prime → (curve x hx).ModEllRepData ℓ
  /-- The local height data of `E_x` computes `h`. -/
  height_eq : ∀ x hx, ((curve x hx).localHeightData (arith x hx) (tate x hx)).height = h x
  /-- `[F_x : ℚ] ≤ 2¹²·3³·5·d` ((E3)–(E5) in the proof of Theorem 1.10). -/
  deg_le : ∀ x hx, Module.finrank ℚ (curve x hx).F ≤ 552960 * d
  /-- `d_mod = [F_mod : ℚ] ≤ d`. -/
  dmod_le : ∀ x hx, Module.finrank ℚ ↥(fieldOfModuli (curve x hx).F (curve x hx).E) ≤ d
  /-- **Corollary 2.2(i)**: `(1/6)·log(q_∀) ≈ ht_{ω_X(D)}` on `K_V`. -/
  htCan_equiv : ((1 / 6 : ℝ) • h) ≈[T.cbsSet K] T.htCan T.tripod
  /-- **Northcott finiteness**. -/
  northcott : ∀ H : ℝ, {x | x ∈ T.cbsSet K ∩ T.ptLE T.tripod d ∧ h x ≤ H}.Finite
  /-- The bound `B_K` on the contribution of the prime `2` to `log(q_∀)`. -/
  B : ℝ
  /-- `B_K ≥ 0`. -/
  B_nonneg : 0 ≤ B
  /-- The contribution of the places over `2` is bounded on `K_V`. -/
  heightEq_two_le : ∀ x hx,
    ((curve x hx).localHeightData (arith x hx) (tate x hx)).heightEq 2 ≤ B
  /-- `E_x` has an `ℓ`-cyclic subgroup scheme. -/
  HasCyclicSubgroup : T.Pt T.tripod → ℕ → Prop
  /-- The number `T_K` of [GenEll], Lemma 3.5. -/
  TK : ℝ
  /-- **[GenEll], Lemma 3.5 with Proposition 3.4, away from `2`**: an `ℓ`-cyclic subgroup
  scheme forces `((ℓ−2)/24)·(log(q_∀) − log(q₂)) ≤ 2·log ℓ + T_K`, where `log(q₂)` is the part of
  `log(q_∀)` supported over `2`. -/
  cyclic_bound : ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d),
    ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ →
    (∀ w ∈ ((curve x hx).localHeightData (arith x hx) (tate x hx)).bad,
      ¬ ℓ ∣ ((curve x hx).localHeightData (arith x hx) (tate x hx)).hv w) →
    HasCyclicSubgroup x ℓ →
    ((ℓ : ℝ) - 2) / 24 *
        (h x - ((curve x hx).localHeightData (arith x hx) (tate x hx)).heightEq 2) ≤
      2 * Real.log ℓ + TK
  /-- **[GenEll], Lemma 3.1(iii)**: (P2), (P4), (P5) imply that the image of the mod-`ℓ`
  representation contains `SL₂(𝔽_ℓ)`. -/
  sl2_of : ∀ x hx (ℓ : ℕ) (hℓ : ℓ.Prime), 5 ≤ ℓ →
    (∀ w ∈ ((curve x hx).localHeightData (arith x hx) (tate x hx)).bad,
      ¬ ℓ ∣ ((curve x hx).localHeightData (arith x hx) (tate x hx)).hv w) →
    ¬ HasCyclicSubgroup x ℓ →
    (∃ w ∈ ((curve x hx).localHeightData (arith x hx) (tate x hx)).bad,
      ((curve x hx).localHeightData (arith x hx) (tate x hx)).p w ≠ 2 ∧
      ((curve x hx).localHeightData (arith x hx) (tate x hx)).p w ≠ ℓ) →
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (modRep x hx ℓ hℓ).rep.range
  /-- **[CanLift], Proposition 2.7** (taxis #10): only finitely many points of bounded
  degree have a once-punctured elliptic curve `X_x` that fails to have the `F_x`-core
  `C_x = X_x/{±1}`. -/
  excCore_finite : {x | ∃ hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d,
    ¬ OrbicurveDataSection.HasCoreUniversally AG (curve x hx).F (curve x hx).E}.Finite
  /-- `log-diff_X(x)` is the normalized degree of the different of `F_tpd`. -/
  logDiff_eq : ∀ x hx,
    T.logDiff T.tripod x = logDifferentDeg ↥(tripodalFieldOf (curve x hx).F (curve x hx).E)
  /-- The conductor invariant of `F_tpd` (away from `2ℓ`) is at most `log-cond_D(x)`. -/
  logCond_ge : ∀ x hx (ℓ : ℕ), ℓ.Prime → 7 ≤ ℓ →
    logConductorDegOf (curve x hx).F (curve x hx).E ((curve x hx).VBadOf ℓ) ≤
      T.logCond T.tripod x
  /-- `log-cond_D(x)` exceeds the conductor invariant of `F_tpd` away from `2ℓ` by at most
  `log(2ℓ)`. -/
  logCond_le : ∀ x hx (ℓ : ℕ), ℓ.Prime → 7 ≤ ℓ →
    T.logCond T.tripod x ≤
      logConductorDegOf (curve x hx).F (curve x hx).E ((curve x hx).VBadOf ℓ) +
        Real.log (2 * ℓ)

end Iut

namespace Iut.Tripod

open WeierstrassCurve NumberField Polynomial
open scoped IntermediateField

theorem logDifferentDeg_eq_of_algEquiv {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] (f : K ≃ₐ[ℚ] L) : logDifferentDeg K = logDifferentDeg L := by
  unfold logDifferentDeg
  rw [absNorm_differentIdeal (K := K), absNorm_differentIdeal (K := L),
    discr_eq_discr_of_algEquiv K f, f.toLinearEquiv.finrank_eq]

/-- `log-diff_ℙ(λ) = log(d_{ℚ(λ)})`. -/
theorem logDiff_eq_logDifferentDeg (x : Pt) : logDiff x = logDifferentDeg (fieldOf x.1) := by
  rw [logDiff_eq_log_absNorm_differentIdeal, logDifferentDeg, deg_eq_finrank]

section Curve

variable (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)

theorem fieldOfModuli_le :
    fieldOfModuli (curveOf x h3 h5).F (curveOf x h3 h5).E ≤ ℚ⟮genC x h3 h5⟯ :=
  IntermediateField.adjoin_simple_le_iff.mpr (j_mem_adjoin x h3 h5)

/-- `λ ∈ F_λ` is integral over `ℚ`. -/
theorem isIntegral_genC : IsIntegral ℚ (genC x h3 h5) :=
  Algebra.IsIntegral.isIntegral _

theorem finrank_adjoin_genC : Module.finrank ℚ ℚ⟮genC x h3 h5⟯ = deg x.1 := by
  rw [(adjoinGenCEquiv x h3 h5).toLinearEquiv.finrank_eq, deg_eq_finrank]

/-- `d_mod = [F_mod : ℚ] ≤ [ℚ(λ) : ℚ]`. -/
theorem dmod_le :
    Module.finrank ℚ ↥(fieldOfModuli (curveOf x h3 h5).F (curveOf x h3 h5).E) ≤ deg x.1 := by
  haveI : FiniteDimensional ℚ ℚ⟮genC x h3 h5⟯ :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_genC x h3 h5)
  rw [← finrank_adjoin_genC x h3 h5]
  exact IntermediateField.finrank_le_of_le_right (fieldOfModuli_le x h3 h5)

theorem logDiff_eq :
    logDiff x = logDifferentDeg ↥(tripodalFieldOf (curveOf x h3 h5).F (curveOf x h3 h5).E) := by
  haveI : FiniteDimensional ℚ ℚ⟮genC x h3 h5⟯ :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_genC x h3 h5)
  rw [logDiff_eq_logDifferentDeg]
  exact (logDifferentDeg_eq_of_algEquiv
    ((IntermediateField.equivOfEq (tripodalFieldOf_eq x h3 h5)).trans
      (adjoinGenCEquiv x h3 h5))).symm

end Curve

theorem sqrtNegOne_sq : sqrtNegOne ^ 2 = -1 :=
  (IsAlgClosed.exists_pow_nat_eq (-1 : Qbar) two_pos).choose_spec

theorem sqrtLam_sq (l : Qbar) : sqrtLam l ^ 2 = l :=
  (IsAlgClosed.exists_pow_nat_eq l two_pos).choose_spec

theorem sqrtOneSubLam_sq (l : Qbar) : sqrtOneSubLam l ^ 2 = 1 - l :=
  (IsAlgClosed.exists_pow_nat_eq (1 - l) two_pos).choose_spec

def TorsionDegreeBound (l : Qbar) (n : ℕ) : Prop :=
  ∀ K : IntermediateField ℚ Qbar, FiniteDimensional ℚ K → l ∈ K →
    Module.finrank ℚ ↥(K ⊔ IntermediateField.adjoin ℚ (torsionCoords l n)) ≤
      (n ^ 2 - 1) * (n ^ 2 - n) * Module.finrank ℚ K

/-- `[K(s) : ℚ] ≤ 2·[K : ℚ]` for `s² ∈ K`. -/
theorem finrank_sup_adjoin_sq_le (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K]
    {s : Qbar} (hs : s ^ 2 ∈ K) :
    Module.finrank ℚ ↥(K ⊔ ℚ⟮s⟯) ≤ 2 * Module.finrank ℚ K := by
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup]
  have hint : IsIntegral K s := (isIntegral s).tower_top
  have h2 : Module.finrank K K⟮s⟯ ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hint]
    have hmin := minpoly.min K s (monic_X_pow_sub_C (⟨s ^ 2, hs⟩ : K) two_ne_zero) (by simp)
    have := natDegree_le_natDegree hmin
    rwa [natDegree_X_pow_sub_C] at this
  calc Module.finrank ℚ ↥(IntermediateField.restrictScalars ℚ K⟮s⟯)
      = Module.finrank ℚ K * Module.finrank K K⟮s⟯ :=
        (Module.finrank_mul_finrank ℚ K K⟮s⟯).symm
    _ ≤ Module.finrank ℚ K * 2 := Nat.mul_le_mul_left _ h2
    _ = 2 * Module.finrank ℚ K := mul_comm _ _

/-- `[ℚ(λ, √−1, √λ, √(1 − λ)) : ℚ] ≤ 8·[ℚ(λ) : ℚ]`. -/
theorem finrank_adjoin_gens_le (l : Qbar) :
    Module.finrank ℚ ↥(IntermediateField.adjoin ℚ {l, sqrtNegOne, sqrtLam l, sqrtOneSubLam l}) ≤
      8 * deg l := by
  have hset : ({l, sqrtNegOne, sqrtLam l, sqrtOneSubLam l} : Set Qbar) =
      (({l} ∪ {sqrtNegOne}) ∪ {sqrtLam l}) ∪ {sqrtOneSubLam l} := by
    ext a
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, or_assoc]
  rw [hset, IntermediateField.adjoin_union, IntermediateField.adjoin_union,
    IntermediateField.adjoin_union]
  haveI : FiniteDimensional ℚ ℚ⟮sqrtNegOne⟯ :=
    IntermediateField.adjoin.finiteDimensional (isIntegral _)
  haveI : FiniteDimensional ℚ ℚ⟮sqrtLam l⟯ :=
    IntermediateField.adjoin.finiteDimensional (isIntegral _)
  have hl : l ∈ ℚ⟮l⟯ := IntermediateField.mem_adjoin_simple_self ℚ l
  have h1 : Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯) ≤ 2 * deg l := by
    rw [deg_eq_finrank]
    exact finrank_sup_adjoin_sq_le _ (by rw [sqrtNegOne_sq]; exact neg_mem (one_mem _))
  have h2 : Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯ ⊔ ℚ⟮sqrtLam l⟯) ≤
      2 * Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯) :=
    finrank_sup_adjoin_sq_le _ (by rw [sqrtLam_sq]; exact le_sup_left (a := ℚ⟮l⟯) hl)
  have h3 : Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯ ⊔ ℚ⟮sqrtLam l⟯ ⊔ ℚ⟮sqrtOneSubLam l⟯) ≤
      2 * Module.finrank ℚ ↥(ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯ ⊔ ℚ⟮sqrtLam l⟯) :=
    finrank_sup_adjoin_sq_le _ (by
      rw [sqrtOneSubLam_sq]
      exact sub_mem (one_mem _)
        (le_sup_left (a := ℚ⟮l⟯ ⊔ ℚ⟮sqrtNegOne⟯) (le_sup_left (a := ℚ⟮l⟯) hl)))
  omega

/-- **The degree bound** `[F_λ : ℚ] ≤ 552960·[ℚ(λ) : ℚ]` ((E3)–(E5) in the proof of IUT IV,
Theorem 1.10), from the torsion degree bounds for `n = 3` and `n = 5`:
`[F_λ : ℚ] ≤ 480·48·8·[ℚ(λ) : ℚ] = 184320·[ℚ(λ) : ℚ]`. -/
theorem deg_le (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)
    (hT3 : TorsionDegreeBound x.1 3) (hT5 : TorsionDegreeBound x.1 5) :
    Module.finrank ℚ (curveOf x h3 h5).F ≤ 552960 * deg x.1 := by
  set K₁ : IntermediateField ℚ Qbar :=
    IntermediateField.adjoin ℚ {x.1, sqrtNegOne, sqrtLam x.1, sqrtOneSubLam x.1} with hK₁
  set K₂ : IntermediateField ℚ Qbar :=
    K₁ ⊔ IntermediateField.adjoin ℚ (torsionCoords x.1 3) with hK₂
  haveI hK₁fin : FiniteDimensional ℚ K₁ := by
    haveI := (Set.toFinite {x.1, sqrtNegOne, sqrtLam x.1, sqrtOneSubLam x.1}).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun y _ ↦ isIntegral y
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (torsionCoords x.1 3)) := by
    haveI := (torsionCoords_finite h3).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun y _ ↦ isIntegral y
  haveI hK₂fin : FiniteDimensional ℚ K₂ := IntermediateField.finiteDimensional_sup _ _
  have hl₁ : x.1 ∈ K₁ := IntermediateField.subset_adjoin _ _ (by simp)
  have hl₂ : x.1 ∈ K₂ := le_sup_left (a := K₁) hl₁
  have hF : fieldOf' x.1 = K₂ ⊔ IntermediateField.adjoin ℚ (torsionCoords x.1 5) := by
    rw [fieldOf', IntermediateField.adjoin_union, IntermediateField.adjoin_union]
  have h1 : Module.finrank ℚ K₁ ≤ 8 * deg x.1 := finrank_adjoin_gens_le x.1
  have h2 : Module.finrank ℚ K₂ ≤ 48 * Module.finrank ℚ K₁ := by
    have := hT3 K₁ hK₁fin hl₁
    norm_num at this
    exact this
  have h5' : Module.finrank ℚ ↥(K₂ ⊔ IntermediateField.adjoin ℚ (torsionCoords x.1 5)) ≤
      480 * Module.finrank ℚ K₂ := by
    have := hT5 K₂ hK₂fin hl₂
    norm_num at this
    exact this
  change Module.finrank ℚ (fieldOf' x.1) ≤ 552960 * deg x.1
  rw [hF]
  omega

section Hypotheses

variable (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)

def LegendreHeightHyp : Prop := ((1 / 6 : ℝ) • P.h) ≈[K.set] htCan

/-- **The `2`-adic bound**: the contribution of the places over `2` to `log(q_∀(E_λ))` is
bounded by `B` on a compactly bounded subset (the places of `F_λ` over `2` lie over the
places of `ℚ(λ)` over `2 ∈ V`, where `|log|λ|_v|`, `|log|λ − 1|_v|` are bounded, and
`ord_w(q_w) = −ord_w(j(E_λ))` with `j = 256(λ² − λ + 1)³/(λ²(λ − 1)²)`). -/
def TwoAdicBoundHyp (B : ℝ) : Prop := ∀ x ∈ K.set, (P.localData x).heightEq 2 ≤ B

/-- **[GenEll], Lemma 3.5 (with Proposition 3.4)**: if `E_λ` has an `ℓ`-cyclic subgroup
scheme then `(ℓ − 2)/24 · log(q_∀) ≤ 2 log ℓ + T_K`. -/
def CyclicBoundHyp (TK : ℝ) : Prop :=
  ∀ x ∈ K.set ∩ ptLE d, ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ →
    (∀ w ∈ (P.localData x).bad, ¬ ℓ ∣ (P.localData x).hv w) →
    (P.curve x).HasCyclicSubgroup ℓ →
    ((ℓ : ℝ) - 2) / 24 * P.h x ≤ 2 * Real.log ℓ + TK

/-- **[GenEll], Lemma 3.5 away from `2`**: if `E_λ` has an `ℓ`-cyclic subgroup scheme and (P2)
holds, then `(ℓ − 2)/24 · (log(q_∀) − log(q₂)) ≤ 2 log ℓ + T_K`, where `log(q₂)` is the part of
`log(q_∀)` supported over `2` (bounded on `K` by `TwoAdicBoundHyp`). This weakening of
`CyclicBoundHyp` is what IUT IV, Corollary 2.2 consumes (`Iut.Corollary22Inputs.cyclic_bound`);
it is proved in `Iut/Tripod/CyclicIsogeny.lean` (`Iut.Tripod.cyclicBoundOdd`). -/
def CyclicBoundOddHyp (TK : ℝ) : Prop :=
  ∀ x ∈ K.set ∩ ptLE d, ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ →
    (∀ w ∈ (P.localData x).bad, ¬ ℓ ∣ (P.localData x).hv w) →
    (P.curve x).HasCyclicSubgroup ℓ →
    ((ℓ : ℝ) - 2) / 24 * (P.h x - (P.localData x).heightEq 2) ≤ 2 * Real.log ℓ + TK

/-- **[GenEll], Lemma 3.1(iii)**: under (P2), (P4), (P5) the image of the mod-`ℓ`
representation contains `SL₂(𝔽_ℓ)`. -/
def SL2ImageHyp : Prop :=
  ∀ (x : Pt) (ℓ : ℕ) (hℓ : ℓ.Prime), 5 ≤ ℓ →
    (∀ w ∈ (P.localData x).bad, ¬ ℓ ∣ (P.localData x).hv w) →
    ¬ (P.curve x).HasCyclicSubgroup ℓ →
    (∃ w ∈ (P.localData x).bad, (P.localData x).p w ≠ 2 ∧ (P.localData x).p w ≠ ℓ) →
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ (P.modRep x ℓ hℓ).rep.range

def LogCondGeHyp : Prop :=
  ∀ (x : Pt) (ℓ : ℕ), ℓ.Prime → 7 ≤ ℓ →
    logConductorDegOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ) ≤ logCond x

/-- **The conductor bound from above**: `log-cond_{{0,1,∞}}(λ)` exceeds the conductor degree
of `F_tpd = ℚ(λ)` away from `2ℓ` by at most `log(2ℓ)` (the places where `λ` meets
`{0, 1, ∞}` of residue characteristic `≠ 2, ℓ` are multiplicative for `E_λ`, since `c₄` is
a unit there; the places over `2` and `ℓ` contribute at most `log 2 + log ℓ`). -/
def LogCondLeHyp : Prop :=
  ∀ (x : Pt) (ℓ : ℕ), ℓ.Prime → 7 ≤ ℓ →
    logCond x ≤
      logConductorDegOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ) + Real.log (2 * ℓ)

/-- **[CanLift], Proposition 2.7**: only finitely many points of bounded degree in `K` have
a once-punctured elliptic curve `X_λ` that fails to have the `F_λ`-core `C_λ = X_λ/{±1}`
(the four exceptional `j`-invariants), relative to an anabelian interface `AG`. Proved for
the model geometry `modelAG Pi1` in `Iut.Tripod.coreFiniteness`. -/
def CoreFinitenessHyp (AG : AnabelianGeometry.{0}) : Prop :=
  {x | ∃ hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d,
    ¬ OrbicurveDataSection.HasCoreUniversally AG (P.curve x).F (P.curve x).E}.Finite

/-- **The facts about the curves of the points not proved in this file**, collected: exactly
the fields of `Iut.CurveInputs` for `curveOf` that are not proved here or in `TwoAdic.lean`,
`LogCond.lean`, `Height.lean` or `Core.lean` — the cyclic-subgroup bound, proved in
`CyclicIsogeny.lean` (`Iut.Tripod.cyclicBoundOdd`). -/
structure CurveFactsProp (TK : ℝ) : Prop where
  /-- [GenEll], Lemma 3.5, away from `2` (proved: `Iut.Tripod.cyclicBoundOdd`). -/
  cyclic : CyclicBoundOddHyp P K d TK

end Hypotheses

section Constructor

variable (sl2Image : ∀ P : CurveProviders, SL2ImageHyp P)
variable (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)

noncomputable def curveInputs {AG : AnabelianGeometry.{0}} {TK : ℝ}
    (CF : CurveFactsProp P K d TK) (hcore : CoreFinitenessHyp P K d AG) (hN : NorthcottHyp)
    (hdeg3 : ∀ x : Pt, TorsionDegreeBound x.1 3) (hdeg5 : ∀ x : Pt, TorsionDegreeBound x.1 5)
    (hh : LegendreHeightHyp P K) (hB : TwoAdicBoundHyp P K (max (4 * K.c) 0))
    (hge : LogCondGeHyp P) (hle : LogCondLeHyp P) :
    CurveInputs tripodTheory AG K d where
  h := P.h
  curve x _ := P.curve x
  arith x _ := P.arith x
  tate x _ := P.tate x
  modRep x _ ℓ hℓ := P.modRep x ℓ hℓ
  height_eq _ _ := rfl
  deg_le x hx := by
    refine (deg_le x _ _ (hdeg3 x) (hdeg5 x)).trans ?_
    exact Nat.mul_le_mul_left _ hx.2
  dmod_le x hx := (dmod_le x _ _).trans hx.2
  htCan_equiv := hh
  northcott := northcott_of_equiv hN K d hh
  B := max (4 * K.c) 0
  B_nonneg := le_max_right _ _
  heightEq_two_le x hx := hB x hx.1
  HasCyclicSubgroup x ℓ := (P.curve x).HasCyclicSubgroup ℓ
  TK := TK
  cyclic_bound := CF.cyclic
  sl2_of x _ ℓ hℓ := sl2Image P x ℓ hℓ
  logDiff_eq x _ := logDiff_eq x _ _
  excCore_finite := hcore
  logCond_ge x _ := hge x
  logCond_le x _ := hle x

end Constructor
end Iut.Tripod

namespace FoundationAudit
open Lean

def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
def stringField (j : Json) (key : String) : Except String String := do
  (← field j key).getStr?
def arrayField (j : Json) (key : String) : Except String (Array Json) := do
  (← field j key).getArr?

-- Preserve actual Name components, including numeric components; do not use String.toName.
partial def encodeName : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => Json.arr #[(encodeName p), Json.str "str", Json.str s]
  | .num p n => Json.arr #[(encodeName p), Json.str "num", toJson n]

partial def decodeName (j : Json) : Except String Name := do
  let a ← j.getArr?
  if a.isEmpty then return .anonymous
  unless a.size == 3 do throw "Invalid Name JSON"
  let p ← decodeName a[0]!
  match ← a[1]!.getStr? with
  | "str" => return .str p (← a[2]!.getStr?)
  | "num" => return .num p (← a[2]!.getNat?)
  | _ => throw "Invalid Name component"

def node (kind : String) (values : List (String × Json)) : Json :=
  Json.mkObj (("kind", Json.str kind) :: values)

partial def encodeLevel : Level → Except String Json
  | .zero => return node "zero" []
  | .succ u => return node "succ" [("arg", ← encodeLevel u)]
  | .max u v => return node "max" [("left", ← encodeLevel u), ("right", ← encodeLevel v)]
  | .imax u v => return node "imax" [("left", ← encodeLevel u), ("right", ← encodeLevel v)]
  | .param n => return node "param" [("name", encodeName n)]
  | .mvar _ => throw "Universe metavariable in compiler type"

partial def decodeLevel (j : Json) : Except String Level := do
  match ← stringField j "kind" with
  | "zero" => return .zero
  | "succ" => return .succ (← decodeLevel (← field j "arg"))
  | "max" => return .max (← decodeLevel (← field j "left")) (← decodeLevel (← field j "right"))
  | "imax" => return .imax (← decodeLevel (← field j "left")) (← decodeLevel (← field j "right"))
  | "param" => return .param (← decodeName (← field j "name"))
  | k => throw s!"Unknown universe kind: {k}"

def encodeBinder : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

def decodeBinder : String → Except String BinderInfo
  | "default" => return .default
  | "implicit" => return .implicit
  | "strictImplicit" => return .strictImplicit
  | "instImplicit" => return .instImplicit
  | k => throw s!"Unknown binder info: {k}"

partial def encodeExpr : Expr → Except String Json
  | .bvar i => return node "bvar" [("index", toJson i)]
  | .sort u => return node "sort" [("level", ← encodeLevel u)]
  | .const n us => return node "const" [("name", encodeName n),
      ("levels", Json.arr (← us.toArray.mapM encodeLevel))]
  | .app f a => return node "app" [("fn", ← encodeExpr f), ("arg", ← encodeExpr a)]
  | .lam n t b bi => return node "lam" [("name", encodeName n),
      ("type", ← encodeExpr t), ("body", ← encodeExpr b), ("binder", toJson (encodeBinder bi))]
  | .forallE n t b bi => return node "forall" [("name", encodeName n),
      ("type", ← encodeExpr t), ("body", ← encodeExpr b), ("binder", toJson (encodeBinder bi))]
  | .letE n t v b nd => return node "let" [("name", encodeName n),
      ("type", ← encodeExpr t), ("value", ← encodeExpr v), ("body", ← encodeExpr b),
      ("nondependent", toJson nd)]
  | .lit (.natVal n) => return node "nat" [("value", toJson n)]
  | .lit (.strVal s) => return node "string" [("value", toJson s)]
  | .mdata _ b => encodeExpr b
  | .proj n i b => return node "proj" [("name", encodeName n), ("index", toJson i),
      ("body", ← encodeExpr b)]
  | .fvar _ => throw "Free variable in compiler declaration type"
  | .mvar _ => throw "Expression metavariable in compiler declaration type"

open Lean Elab Term Meta

def checked {α : Type} (x : Except String α) : MetaM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError "{e}"

def namesFromJson (j : Json) : MetaM (List Name) := do
  return (← checked ((← checked j.getArr?).mapM decodeName)).toList

def absoluteEnv (key : String) : MetaM String := do
  let some p ← IO.getEnv key | throwError "Missing environment variable {key}"
  unless p.startsWith "/" do throwError "Expected absolute path: {key}"
  return p

def moduleOf (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  env.header.moduleNames[index.toNat]?

def standardAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

def ensureStandard (label : String) (axs : Array Name) : MetaM Unit := do
  for ax in axs do
    unless standardAxioms.contains ax do throwError "Unexpected axiom in {label}: {ax}"

end FoundationAudit

namespace CurveInputsExpressionComparison
open Lean Elab Term Meta FoundationAudit

def relocateName (maps : Array (Name × Name)) (n : Name) : Except String Name := do
  if let some pair := maps.find? (fun pair => pair.1 == n) then
    return pair.2
  if (`Iut.Tripod).isPrefixOf n then
    return n.replacePrefix `Iut.Tripod `AbcAdaptation.Tripod
  if #[`Iut, `Genl, `TateCurvesTheta, `DiscrepancyEquiv, `DiscrepancyLE].any (·.isPrefixOf n) then
    return `AbcAdaptation.Reference ++ n
  if (`_private).isPrefixOf n then throw s!"Unmapped private reference constant {n}"
  return n

/- Decode a kernel expression from the reference environment. -/
partial def relocateExpr (maps : Array (Name × Name)) (j : Json) : Except String Expr := do
  let recur := relocateExpr maps
  let relocate := relocateName maps
  match ← stringField j "kind" with
  | "bvar" => return .bvar (← (← field j "index").getNat?)
  | "sort" => return .sort (← decodeLevel (← field j "level"))
  | "const" =>
    let n ← decodeName (← field j "name")
    let us ← (← arrayField j "levels").mapM decodeLevel
    return .const (← relocate n) us.toList
  | "app" => return .app (← recur (← field j "fn")) (← recur (← field j "arg"))
  | "lam" => return .lam (← decodeName (← field j "name")) (← recur (← field j "type")) (← recur (← field j "body")) (← decodeBinder (← stringField j "binder"))
  | "forall" => return .forallE (← decodeName (← field j "name")) (← recur (← field j "type")) (← recur (← field j "body")) (← decodeBinder (← stringField j "binder"))
  | "let" => return .letE (← decodeName (← field j "name")) (← recur (← field j "type")) (← recur (← field j "value")) (← recur (← field j "body")) (← (← field j "nondependent").getBool?)
  | "nat" => return .lit (.natVal (← (← field j "value").getNat?))
  | "string" => return .lit (.strVal (← stringField j "value"))
  | "proj" => return .proj (← relocate (← decodeName (← field j "name"))) (← (← field j "index").getNat?) (← recur (← field j "body"))
  | k => throw s!"Unsupported actual Expr kind {k}"

def requireClosed (label : String) (e : Expr) : MetaM Unit := do
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then throwError "Open expression {label}"

def kernelCheck (label : String) (e : Expr) : MetaM Expr := do
  requireClosed label e
  match Kernel.check (← getEnv) {} e with
  | .ok t => return t
  | .error ex => throwKernelException ex

def kernelEq (label : String) (e f : Expr) : MetaM Unit := do
  let et ← kernelCheck label e
  let ft ← kernelCheck label f
  for (a,b) in #[(et,ft),(e,f)] do
    match Kernel.isDefEq (← getEnv) {} a b with
    | .ok true => pure ()
    | .ok false => throwError "Kernel inequality {label}"
    | .error ex => throwKernelException ex

partial def outerBinderPlacement (e : Expr) : Array String :=
  match e with
  | .forallE _ _ body binder => #[encodeBinder binder] ++ outerBinderPlacement body
  | .mdata _ body => outerBinderPlacement body
  | _ => #[]

def sourceAxioms (row : Json) (key : String) : MetaM (Array String) := do
  let recorded ← checked (row.getObjValAs? (Array String) key)
  let allowed := standardAxioms.map Name.toString
  unless recorded.all (allowed.contains ·) do
    throwError "Unexpected source axioms in {key}: {recorded}"
  return recorded

end CurveInputsExpressionComparison

namespace CurveInputsAudit

open Lean Elab Term Meta FoundationAudit CurveInputsExpressionComparison

private def fieldNames : Array Name :=
  #[`h, `curve, `arith, `tate, `modRep, `height_eq, `deg_le, `dmod_le, `htCan_equiv,
    `northcott, `B, `B_nonneg, `heightEq_two_le, `HasCyclicSubgroup, `TK, `cyclic_bound,
    `sl2_of, `excCore_finite, `logDiff_eq, `logCond_ge, `logCond_le]

structure Assignment where
  field : Name
  type : Expr
  value : Expr
  inputs : Array Name
  projectUses : Array Name

structure Constructor where
  type : Expr
  axioms : Array Name
  assignments : Array Assignment

private def ownsProjectConstant (name : Name) : Bool :=
  #[`Iut, `Genl, `TateCurvesTheta, `AbcAdaptation, `DiscrepancyEquiv, `DiscrepancyLE].any
    (·.isPrefixOf name)

private def requiredInputs (field : Name) : Array Name :=
  match field with
  | `deg_le => #[`hdeg3, `hdeg5]
  | `htCan_equiv => #[`hh]
  | `northcott => #[`hN, `hh]
  | `heightEq_two_le => #[`hB]
  | `cyclic_bound => #[`CF]
  | `excCore_finite => #[`hcore]
  | `logCond_ge => #[`hge]
  | `logCond_le => #[`hle]
  | _ => #[]

private def requiredProjectUse (field : Name) : Option Name :=
  match field with
  | `h => some `Iut.Tripod.CurveProviders.h
  | `curve => some `Iut.Tripod.CurveProviders.curve
  | `arith => some `Iut.Tripod.CurveProviders.arith
  | `tate => some `Iut.Tripod.CurveProviders.tate
  | `modRep => some `Iut.Tripod.CurveProviders.modRep
  | `deg_le => some `Iut.Tripod.deg_le
  | `dmod_le => some `Iut.Tripod.dmod_le
  | `northcott => some `Iut.Tripod.northcott_of_equiv
  | `HasCyclicSubgroup => some `Iut.EllipticCurveData.HasCyclicSubgroup
  | `cyclic_bound => some `Iut.Tripod.CurveFactsProp.cyclic
  | `sl2_of => some `Iut.Tripod.sl2Image
  | `logDiff_eq => some `Iut.Tripod.logDiff_eq
  | _ => none

def projectName (name : Name) : Name :=
  if (`Iut.Tripod).isPrefixOf name then
    name.replacePrefix `Iut.Tripod `AbcAdaptation.Tripod
  else if #[`Iut, `Genl, `TateCurvesTheta, `DiscrepancyEquiv, `DiscrepancyLE].any
      (·.isPrefixOf name) then
    `AbcAdaptation.Reference ++ name
  else name

def readConstructor (name recordName : Name) (translate : Name → Name)
    (suppliedImage := false) : MetaM Constructor := do
  let env ← getEnv
  let some record := getStructureInfo? env recordName |
    throwError "Missing structure metadata for {recordName}"
  unless record.fieldNames == fieldNames do
    throwError "Unexpected CurveInputs fields {record.fieldNames}"
  let .defnInfo decl ← getConstInfo name |
    throwError "Expected the CurveInputs constructor definition {name}"
  unless decl.levelParams.isEmpty do throwError "Unexpected constructor universe parameters"
  let axioms ← collectAxioms name
  ensureStandard name.toString axioms
  let inferred ← kernelCheck name.toString decl.value
  kernelEq "constructor declared type" inferred decl.type
  let assignments ← lambdaTelescope decl.value fun binders body => do
    let names ← binders.mapM fun binder => return (← binder.fvarId!.getDecl).userName
    let expectedArity := if suppliedImage then 15 else 14
    unless names.size == expectedArity && (!suppliedImage || names[0]! == `sl2Image) do
      throwError "Unexpected constructor binders {names}"
    let body := body.consumeMData
    let .const ctorName levels := body.getAppFn |
      throwError "Expected a CurveInputs constructor application"
    let ctor ← getConstInfoCtor ctorName
    let arguments := body.getAppArgs
    unless ctor.induct == recordName && arguments.size == ctor.numParams + fieldNames.size do
      throwError "Unexpected record constructor {ctorName} with {arguments.size} arguments"
    let mut assignments : Array Assignment := #[]
    for index in [:fieldNames.size] do
      let field := fieldNames[index]!
      let offset := ctor.numParams + index
      let remainingType ← instantiateForall
        (ctor.type.instantiateLevelParams ctor.levelParams levels) (arguments.extract 0 offset)
      let .forallE _ fieldType _ _ := remainingType |
        throwError "Could not instantiate the dependent type of {field}"
      let value ← deltaExpand arguments[offset]!
        (fun n => name.isPrefixOf (privateToUserName n)) (allowOpaque := true)
      let projectUses := (value.getUsedConstants.map privateToUserName).filter ownsProjectConstant
      let mut inputs : Array Name := #[]
      for binder in [:binders.size] do
        if value.containsFVar binders[binder]!.fvarId! then
          inputs := inputs.push names[binder]!
      for input in requiredInputs field do
        unless inputs.contains input do throwError "Field {field} did not use {input}"
      if suppliedImage then
        unless (inputs.contains `sl2Image) == (field == `sl2_of) do
          throwError "Unexpected use of the explicit SL2 supplier in {field}"
      if let some expected := requiredProjectUse field then
        unless suppliedImage && field == `sl2_of do
          let expected := translate expected
          let isProjection : Expr → Bool
            | .proj base index _ =>
              ((getStructureInfo? env base).bind fun info => info.fieldNames[index]?).any
                (fun fieldName => base ++ fieldName == expected)
            | _ => false
          unless projectUses.contains expected || (value.find? isProjection).isSome do
            throwError "Field {field} did not use {expected}"
      let type ← mkForallFVars binders fieldType
      let value ← mkLambdaFVars binders value
      requireClosed s!"type of {field}" type
      requireClosed s!"value of {field}" value
      assignments := assignments.push { field, type, value, inputs, projectUses }
    return assignments
  return { type := decl.type, axioms, assignments }

def exportConstructor (name owner : Name) (constructor : Constructor)
    (suppliedImage := false) : MetaM Json := do
  let rows ← constructor.assignments.mapM fun field => do
    return Json.mkObj [
      ("field", toJson field.field.toString),
      ("type", ← checked (encodeExpr field.type)),
      ("value", ← checked (encodeExpr field.value)),
      ("inputs", toJson (field.inputs.map Name.toString)),
      ("projectUses", Json.arr (field.projectUses.map encodeName))]
  return Json.mkObj [
    ("schema", toJson "tripod-curve-inputs/v1"),
    ("compiler", toJson Lean.versionString),
    ("constructor", toJson name.toString),
    ("owner", toJson owner.toString),
    ("explicitSL2Supplier", toJson suppliedImage),
    ("type", ← checked (encodeExpr constructor.type)),
    ("axioms", toJson (constructor.axioms.map Name.toString)),
    ("fields", Json.arr rows)]

end CurveInputsAudit

open Lean Elab Term Meta FoundationAudit CurveInputsAudit CurveInputsExpressionComparison in
run_meta do
  unless Lean.versionString == "4.35.0-rc3" do throwError "Expected Lean 4.35.0-rc3"
  let name := ``Iut.Tripod.curveInputs
  let env ← getEnv
  unless (env.getModuleIdxFor? name).isNone do
    throwError "Expected a constructor elaborated in this source replay"
  let constructor ← readConstructor name ``Iut.CurveInputs id (suppliedImage := true)
  let .forallE `sl2Image supplyType _ .default := constructor.type.consumeMData |
    throwError "Missing the explicit SL2 supplier"
  let provider := Lean.mkConst ``Iut.Tripod.CurveProviders
  let expected := Expr.forallE `P provider
    (.app (Lean.mkConst ``Iut.Tripod.SL2ImageHyp) (.bvar 0)) .default
  kernelEq "source SL2 supplier type" supplyType expected
  let facts ← exportConstructor name env.mainModule constructor (suppliedImage := true)
  let path ← absoluteEnv "TRIPOD_CURVE_INPUTS_FACTS"
  IO.FS.writeFile path (facts.compress ++ "\n")
  logInfo m!"Exported {constructor.assignments.size} source replay fields and one explicit SL2 supplier"

#print axioms Iut.Tripod.curveInputs
