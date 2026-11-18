/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths: Iut/Concrete/Existence.lean, Iut/Cor312/ThetaData/Orbicurve.lean and Iut/Concrete/CyclicSubgroup.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_LocalHeightDataAssembly
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Corollary22

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

universe u

open NumberField WeierstrassCurve

namespace OrbicurveDataSection

variable (AG : AnabelianGeometry.{u})
variable (F : Type u) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]

/-- **`X_F/{±1}` is the core of `X_F` after every extension of the base field** (of
characteristic `0`): for every embedding `F → K`, `C_K` is the `K`-core of `X_K`. This is the form
in which the core condition of IUT I, Definition 3.1(d) (over the `ℓ`-torsion field) is supplied
to the existence of Θ-data; for non-exceptional `j(E)` it follows from [CanLift], Proposition 2.7
over `K` (`j(E_K) = j(E)`), without any base-change property of cores. -/
def HasCoreUniversally : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (f : F →+* K),
    AG.HasCore (AG.baseChange f (AG.oncePunctured E)) (AG.baseChange f (CF AG F E))

end OrbicurveDataSection

namespace EllipticCurveData

open scoped Classical in
variable (C : EllipticCurveData.{u}) in
/-- `E/F` has an **`ℓ`-cyclic subgroup scheme**: a `Gal(F̄/F)`-stable subgroup of `E(F̄)` of
order `ℓ`. -/
def HasCyclicSubgroup (ℓ : ℕ) : Prop :=
  ∃ H : AddSubgroup (Affine.Point (Affine.baseChange C.E C.Fbar)),
    Nat.card H = ℓ ∧ ∀ σ : C.Fbar ≃ₐ[C.F] C.Fbar, ∀ P ∈ H, galPointMap C.F C.E C.Fbar σ P ∈ H

end EllipticCurveData

variable (T : Genl.HeightTheory) (AG : AnabelianGeometry.{u})

/-- **The inputs of IUT IV, Corollary 2.2 in terms of the curves of the points**: to each
point `x` of `K_V ∩ U_X(ℚ̄)^{≤d}` is attached an elliptic curve `E_x` over the number
field `F_x = F_tpd(√−1, E_x[15])` with its arithmetic, Tate parameters and mod-`ℓ`
representations, and the height-theoretic facts of [GenEll] relating `x` to `E_x`. The
local height data and the image condition (P6) are *computed* from the curve
(`toCorollary22Inputs`). -/
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

variable {T AG}

namespace CurveInputs

variable {K : T.CBS} {d : ℕ} (CI : CurveInputs.{u} T AG K d)

/-- The points whose once-punctured elliptic curve fails to have an `F`-core. -/
def excCore : Set (T.Pt T.tripod) :=
  {x | ∃ hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d,
    ¬ OrbicurveDataSection.HasCoreUniversally AG (CI.curve x hx).F (CI.curve x hx).E}

/-- The inputs of Corollary 2.2 derived from the curves. -/
noncomputable def toCorollary22Inputs : Corollary22Inputs T K d where
  h := CI.h
  localData x hx := (CI.curve x hx).localHeightData (CI.arith x hx) (CI.tate x hx)
  localData_height := CI.height_eq
  localData_deg_le := CI.deg_le
  htCan_equiv := CI.htCan_equiv
  northcott := CI.northcott
  B := CI.B
  B_nonneg := CI.B_nonneg
  heightEq_two_le := CI.heightEq_two_le
  HasCyclicSubgroup := CI.HasCyclicSubgroup
  TK := CI.TK
  cyclic_bound := CI.cyclic_bound
  SL2Image x ℓ := ∀ hx (hℓ : ℓ.Prime), ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ),
    A.toGL ∈ (CI.modRep x hx ℓ hℓ).rep.range
  sl2_of x hx ℓ hp h5 hP2 hcyc hP5 _ hp' := CI.sl2_of x hx ℓ hp' h5 hP2 hcyc hP5
  excCore := CI.excCore
  excCore_finite := CI.excCore_finite.subset Set.inter_subset_left

end CurveInputs
end AbcAdaptation.Reference.Iut
