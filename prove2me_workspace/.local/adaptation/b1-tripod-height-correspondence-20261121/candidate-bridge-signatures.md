# Prove2Me 适配候选桥梁的完整 Lean 签名

声明名和源码行号与证据表逐项对应。定理摘录保留到证明分隔符之前，结构摘录保留全部字段。命名空间、作用域及参与泛化的 `variable` 均取自同一固定提交。 [§4.1 候选桥梁证据表](../../../../docs/开发计划.Prove2Me适配.md#候选桥梁的来源与目标端用途)

<a id="iut-tripod-curves-fieldof-eq"></a>

## `Iut.Tripod.curves_fieldOf_eq`

[Iut/Tripod/GeneralPosition.lean:52](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/GeneralPosition.lean#L52)

```lean
namespace Iut.Tripod

open Genl.Curves Belyi.CurveField Heights.Curve NumberField
open scoped IntermediateField

theorem curves_fieldOf_eq (y : Genl.Curves.tripod.Pt) : y.1.fieldOf = fieldOf (ptEquiv y).1
```

<a id="iut-tripod-exists-abs-htcan-sub-le"></a>

## `Iut.Tripod.exists_abs_htCan_sub_le`

[Iut/Tripod/GeneralPosition.lean:72](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/GeneralPosition.lean#L72)

```lean
namespace Iut.Tripod

open Genl.Curves Belyi.CurveField Heights.Curve NumberField
open scoped IntermediateField

theorem exists_abs_htCan_sub_le :
    ∃ C, ∀ y : Genl.Curves.tripod.Pt,
      |divHeight Genl.Curves.tripod.logCanon y.1 - htCan (ptEquiv y)| ≤ C
```

<a id="iut-tripod-curves-logcond-eq"></a>

## `Iut.Tripod.curves_logCond_eq`

[Iut/Tripod/GeneralPosition.lean:108](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/GeneralPosition.lean#L108)

```lean
namespace Iut.Tripod

open Genl.Curves Belyi.CurveField Heights.Curve NumberField
open scoped IntermediateField

theorem curves_logCond_eq (y : Genl.Curves.tripod.Pt) :
    theory.logCond Genl.Curves.tripod y = logCond (ptEquiv y)
```

<a id="iut-tripod-mem-set-of-bounds"></a>

## `Iut.Tripod.mem_set_of_bounds`

[Iut/Tripod/GeneralPosition.lean:170](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/GeneralPosition.lean#L170)

```lean
namespace Iut.Tripod

open Genl.Curves Belyi.CurveField Heights.Curve NumberField
open scoped IntermediateField

theorem mem_set_of_bounds {F : IntermediateField ℚ Qbar} [FiniteDimensional ℚ F] (z : Pt)
    (hF : F = ℚ⟮z.1⟯) (a : F) (ha : (a : Qbar) = z.1) (K : CBSData) (d : ℕ)
    (hd : Module.finrank ℚ F ≤ d)
    (hp : ∀ p ∈ K.V, ∀ τ : F →+* PadicAlgCl (p : ℕ),
      |Real.log ‖τ a‖| ≤ K.c ∧ |Real.log ‖τ a - 1‖| ≤ K.c)
    (hσ : ∀ σ : F →+* ℂ, |Real.log ‖σ a‖| ≤ K.c ∧ |Real.log ‖σ a - 1‖| ≤ K.c) :
    z ∈ (cbsOf K d).set
```

<a id="genl-curves-nonempty-belyidescent"></a>

## `Genl.Curves.nonempty_belyiDescent`

[Genl/Curves/BelyiDescent.lean:248](https://github.com/lana-agents/genl/blob/ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf/Genl/Curves/BelyiDescent.lean#L248)

```lean
namespace Genl.Curves

open Belyi.CurveField Belyi.CurveField.Divisor Heights.Curve Heights.Absolute Filter
open scoped IntermediateField

open Classical in

theorem nonempty_belyiDescent (X : Curve) (hX : theory.Hyperbolic X)
    (hD : theory.DivisorFree X) (d : ℕ) (ε : ℝ)
    (hfail : ¬(theory.htCan X ≲[theory.ptEQ X d] (1 + ε) • theory.logDiff X)) :
    Nonempty (theory.BelyiDescent X d ε)
```

<a id="genl-curves-nonempty-covering"></a>

## `Genl.Curves.nonempty_covering`

[Genl/Curves/Covering.lean:243](https://github.com/lana-agents/genl/blob/ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf/Genl/Curves/Covering.lean#L243)

```lean
namespace Genl.Curves

open Belyi.CurveField Belyi.CurveField.Divisor Heights.Curve Heights.Absolute Module

open Classical in

theorem nonempty_covering (X : Curve) (hX : theory.Hyperbolic X) (d : ℕ) (ε' : ℝ)
    (hε' : 0 < ε') : Nonempty (theory.Covering X d ε')
```

<a id="heights-curve-logcondof-le-divheight"></a>

## `Heights.Curve.logCondOf_le_divHeight`

[Heights/Curve/CondDivisor.lean:61](https://github.com/lana-agents/heights/blob/721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/Curve/CondDivisor.lean#L61)

```lean
namespace Heights.Curve

open Belyi.CurveField Belyi.CurveField.Divisor Heights.Absolute NumberField
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

theorem logCondOf_le_divHeight (E : Divisor K) (hE : 0 ≤ E) (G : Finset K)
    (hG : ∀ P : Place K, E P = 0 → ∀ g ∈ G, g ∈ P.1) :
    ∃ C, ∀ x : QbarPoint K, (∀ g ∈ G, g ∈ x.P.1) → logCondOf G x ≤ divHeight E x + C
```

<a id="heights-curve-logdisc-le-of-eq-adjoin"></a>

## `Heights.Curve.logDisc_le_of_eq_adjoin`

[Heights/Curve/KummerPoint.lean:45](https://github.com/lana-agents/heights/blob/721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/Curve/KummerPoint.lean#L45)

```lean
namespace Heights.Curve

open NumberField Heights.Different Heights.Absolute

theorem logDisc_le_of_eq_adjoin {F L : IntermediateField ℚ Qbar} [FiniteDimensional ℚ F]
    [FiniteDimensional ℚ L] (hFL : F ≤ L) {N : ℕ} (hN : 0 < N) {c : F} {a b : Qbar}
    (ha : a ^ N = c) (hb : b ^ N = 1 - c)
    (hL : L = (IntermediateField.adjoin F {a, b}).restrictScalars ℚ) (G : Finset F)
    (hG : ∀ u : FinitePlace F, u ∉ meets G → u c = 1 ∧ u (1 - c) = 1) :
    logDisc L ≤ logDisc F + cond G + kummerConst N
```

<a id="belyi-curvefield-exists-isbelyi-notmem-belyicusps"></a>

## `Belyi.CurveField.exists_isBelyi_notMem_belyiCusps`

[Belyi/CurveField/NoncriticalBridge.lean:49](https://github.com/lana-agents/belyi/blob/9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8/Belyi/CurveField/NoncriticalBridge.lean#L49)

```lean
namespace Belyi.CurveField

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

theorem exists_isBelyi_notMem_belyiCusps (T : Finset (Place K)) :
    ∃ φ : K, IsBelyi φ ∧ ∀ P ∈ T, P ∉ belyiCusps φ
```

<a id="belyi-noncriticalp1-normalize-step"></a>

## `Belyi.NoncriticalP1.normalize_step`

[Belyi/NoncriticalP1/Reduction.lean:155](https://github.com/lana-agents/belyi/blob/9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8/Belyi/NoncriticalP1/Reduction.lean#L155) · [迁移签名的内核类型](../prove2me_workspace/.local/adaptation/fermat-noncritical-p1-20261114/upload-elaborated-types.json#L3) · [目标端回执](../prove2me_workspace/.local/adaptation/fermat-noncritical-p1-20261114/existing-types-leaf-result.json)

```lean
namespace Belyi.NoncriticalP1

open Polynomial IntermediateField

theorem normalize_step (T : Finset Qbar) (hT : IsGalStable T) {τ : ℚ} (hτ : (τ : Qbar) ∉ T) :
    ∃ (u : ElemMap) (T₁ : Finset Qbar), IsGalStable T₁ ∧ (∀ y ∈ T₁, ‖ι y‖ ≤ 1) ∧
      (∀ d, 1 ≤ d → (∀ t ∈ T, deg t ≤ d) →
        (∀ y ∈ T₁, deg y ≤ d) ∧
        (2 ≤ d → (T₁.filter fun y => deg y = d).card ≤ (T.filter fun t => deg t = d).card)) ∧
      ∀ hs, IsNoncriticalBelyi hs (withInf T₁) (ofRat 9) →
        IsNoncriticalBelyi (u :: hs) (withInf T) (ofRat τ)
```

<a id="belyi-noncriticalp1-exists-isnoncriticalbelyi-rat"></a>

## `Belyi.NoncriticalP1.exists_isNoncriticalBelyi_rat`

[Belyi/NoncriticalP1/Rational.lean:130](https://github.com/lana-agents/belyi/blob/9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8/Belyi/NoncriticalP1/Rational.lean#L130) · [迁移签名的内核类型](../prove2me_workspace/.local/adaptation/fermat-noncritical-rational-split-20261115/compiler-types.json#L7) · [目标端回执](../prove2me_workspace/.local/adaptation/fermat-noncritical-rational-split-20261115/source-signature-types-v1-result.json)

```lean
namespace Belyi.NoncriticalP1

open Polynomial

theorem exists_isNoncriticalBelyi_rat (T : Finset ℚ) (τ : ℚ) (hT : ∀ t ∈ T, |t| ≤ 1)
    (hτ : 9 ≤ τ) :
    ∃ hs : List ElemMap, IsNoncriticalBelyi hs (insert none (ofRat '' (T : Set ℚ))) (ofRat τ)
```

<a id="belyi-noncriticalp1-minpoly-step"></a>

## `Belyi.NoncriticalP1.minpoly_step`

[Belyi/NoncriticalP1/Reduction.lean:219](https://github.com/lana-agents/belyi/blob/9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8/Belyi/NoncriticalP1/Reduction.lean#L219) · [迁移签名的内核类型](../prove2me_workspace/.local/adaptation/fermat-noncritical-p1-20261114/upload-elaborated-types.json#L9) · [目标端回执](../prove2me_workspace/.local/adaptation/fermat-noncritical-p1-20261114/existing-types-leaf-result.json)

```lean
namespace Belyi.NoncriticalP1

open Polynomial IntermediateField

theorem minpoly_step (T : Finset Qbar) (hT : IsGalStable T) (hbd : ∀ y ∈ T, ‖ι y‖ ≤ 1)
    {d n : ℕ} (hd : 2 ≤ d) (hdeg : ∀ y ∈ T, deg y ≤ d)
    (hcard : (T.filter fun y => deg y = d).card ≤ n + 1) {σ₀ : Qbar} (hσ₀ : σ₀ ∈ T)
    (hσ₀d : deg σ₀ = d) :
    ∃ (T₂ : Finset Qbar) (τ₂ : ℚ), IsGalStable T₂ ∧ (τ₂ : Qbar) ∉ T₂ ∧
      (∀ y ∈ T₂, deg y ≤ d) ∧ (T₂.filter fun y => deg y = d).card ≤ n ∧
      ∃ u : ElemMap, ∀ hs, IsNoncriticalBelyi hs (withInf T₂) (ofRat τ₂) →
        IsNoncriticalBelyi (u :: hs) (withInf T) (ofRat 9)
```

<a id="iut-tripod-abc-of-variant"></a>

## `Iut.Tripod.abc_of_variant`

[Iut/Tripod/Main.lean:129](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/Main.lean#L129)

```lean
namespace Iut.Tripod

open Iut Iut.EllipticCurveData Iut.Anabelian NumberField Iut.LocalConstruct
open scoped Classical


variable (Pi1 : EtalePi1Theory.{0}) (Tp : TemperedPi1Theory Pi1)

theorem abc_of_variant
    (h312 : ∀ (D : InitialThetaData (modelAG Pi1) (modelTG Pi1 Tp)) (LT : LocalTheory.{0, 0} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      Corollary312Variant (concreteVariantData.{0, 0} D LT TL QI)) :
    tripodTheory.StatementII
```

<a id="iut-anabelian-canlift27"></a>

## `Iut.Anabelian.canLift27`

[Iut/Tripod/ClassicalAbcGenuineCanLift.lean:28](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/ClassicalAbcGenuineCanLift.lean#L28)

```lean
namespace Iut.Anabelian

theorem canLift27 : AffOrbicurve.CanLift27.{0}
```

<a id="iut-corollary22inputs"></a>

## `Iut.Corollary22Inputs`

[Iut/Implication/Corollary22.lean:284](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Implication/Corollary22.lean#L284) · [原内核表达式](../prove2me_workspace/.local/adaptation/c2-complete-inputs-20261116/source-original-exprs.json#L221) · [目标端类型比较回执](../prove2me_workspace/.local/adaptation/main-chain-open-20261116/c22-current-full44-two-values-v34-result.json)

```lean
namespace Iut

universe u v w

open Finset Real

variable (T : Genl.HeightTheory)

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
```

<a id="iut-thetadataexistence"></a>

## `Iut.ThetaDataExistence`

[Iut/Implication/Corollary22.lean:357](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Implication/Corollary22.lean#L357) · [原内核表达式](../prove2me_workspace/.local/adaptation/c2-complete-inputs-20261116/source-original-exprs.json#L319) · [目标端类型比较回执](../prove2me_workspace/.local/adaptation/main-chain-open-20261116/c22-current-full44-two-values-v34-result.json)

```lean
namespace Iut

universe u v w

open Finset Real

variable (T : Genl.HeightTheory)

variable {T}
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

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
```

<a id="iut-theorem110invariants-localestimate"></a>

## `Iut.Theorem110Invariants.LocalEstimate`

[Iut/Implication/LogVolumeBound.lean:69](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Implication/LogVolumeBound.lean#L69) · [原内核表达式](../prove2me_workspace/.local/adaptation/reference-main-bound-carriers-20261115/original-exprs.json#L1807454) · [目标端类型比较回执](../prove2me_workspace/.local/adaptation/reference-main-bound-carriers-20261115/main5-log32-current-structure-source-v27-result.json)

```lean
namespace Iut

universe u v

open NumberField

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

namespace Theorem110Invariants

variable {X : Corollary312VariantData.{u, v} AG TG} (inv : Theorem110Invariants X)

structure LocalEstimate : Type (max u v) where
  /-- The containing hull region at capsule `i` and rational place `v_ℚ`
  (`p^{⌊λ − d_I − a_I⌋ − b_I}·(R_I)^∼`, resp. `(R_I)^∼`, resp. `π^{j+1}·B_I`). -/
  cont : ∀ (i : Fin X.rhsData.container.proc.length) (vQ : RationalPlace),
    Set (X.rhsData.container.packet i vQ).Total
  /-- Each container belongs to the class of hull regions of the hull system (a region
  `a·O` with all components of `a` units; at `∞` a real radial scaling of `B_I`). -/
  cont_mem_hullRegions : ∀ i vQ, cont i vQ ∈ (X.rhsData.hull.system i vQ).HullRegions
  /-- The theta-pilot region (the union of the images under (Ind1)–(Ind3)) is contained
  in the container: the inclusions `φ(p^λ·(R_I)^∼) ⊆ …` of Proposition 1.4(iii),(iv)
  and `⊗ m_i ∈ π^{|I|}·B_I` of Proposition 1.5(iv). -/
  thetaPilot_subset : ∀ i vQ, (X.rhsData.thetaPilot i).region vQ ⊆ cont i vQ
  /-- Away from the distinguished primes the container is the holomorphic integral
  structure (Proposition 1.4(iv): `φ((R_I)^∼) ⊆ (R_I)^∼`). -/
  cont_eq_integral : ∀ i (p : Nat.Primes), (p : ℕ) ∉ inv.dst →
    cont i (.finite p) = (X.rhsData.container.packet i (.finite p)).integralRegion
  /-- Step (v): at a distinguished prime the packet log-volume of the container is
  bounded by `capsuleBound` (Proposition 1.4(iii), (R4), and the weighted average of
  Proposition 1.7). -/
  vol_finite : ∀ i (p : Nat.Primes), (p : ℕ) ∈ inv.dst →
    X.rhsData.vol.packetVol i (.finite p) (cont i (.finite p)) ≤
      inv.capsuleBound (X.rhsData.container.proc.capsule i).card p
  /-- Step (vii): at the archimedean place the packet log-volume of the container is at
  most `(j+1)·log π` (Proposition 1.5(iii),(iv) and the normalization `μ(B_I) = 0`). -/
  vol_infinite : ∀ i,
    X.rhsData.vol.packetVol i .infinite (cont i .infinite) ≤
      (X.rhsData.container.proc.capsule i).card * Real.log Real.pi
  /-- Monotonicity of the packet log-volume between hull regions (a law of Haar
  measure for regions of finite nonzero volume). -/
  packetVol_mono : ∀ i vQ (U V : Set (X.rhsData.container.packet i vQ).Total),
    (X.rhsData.container.packet i vQ).IsHullRegion U →
    (X.rhsData.container.packet i vQ).IsHullRegion V → U ⊆ V →
    X.rhsData.vol.packetVol i vQ U ≤ X.rhsData.vol.packetVol i vQ V
```
