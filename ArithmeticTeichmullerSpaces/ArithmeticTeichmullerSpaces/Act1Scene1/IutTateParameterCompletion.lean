import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompletionSource
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.Basic
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.TateFamily
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.BadPlaceNorm

namespace JoshiTeich.Act1Scene1

open WeierstrassCurve
open NumberField
open TateCurvesTheta
open scoped Valued

universe u

noncomputable section

/-!
source-id: IUT-COR312-TATE-PARAMETER-COMPLETION
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/TateStructure.lean`,
`refer/iut/Iut/Cor312/ThetaData/TateFamily.lean`, and
`refer/iut/Iut/Concrete/ThetaLocalConstruct/TateCompat.lean`;
completion comparison is ported from
`refer/iut/Iut/Concrete/ThetaLocalConstruct/EmbedCompletion.lean`.
fidelity: transports a Tate parameter across the canonical completion map,
proves compatibility of its `j`-invariant, and recovers its `q` parameter from
the `j`-invariant equality.
boundary: Scene1/Derived
-/

def iutEmbedTateParameter
    {F Kt : Type u} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
    [Algebra F Kt] {v : NumberField.FinitePlace Kt} {w : NumberField.FinitePlace F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (t : TateParameter (w.maximalIdeal.adicCompletion F)) :
    TateParameter (v.maximalIdeal.adicCompletion Kt) where
  q := Units.map (iutEmbedCompletion hvw).toMonoidHom t.q
  norm_lt_one := by
    rw [Units.coe_map]
    exact (iutEmbedCompletion_norm_lt_one_iff hvw (t.q : _)).2 t.norm_lt_one

lemma iutEmbedTateParameter_q_coe
    {F Kt : Type u} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
    [Algebra F Kt] {v : NumberField.FinitePlace Kt} {w : NumberField.FinitePlace F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (t : TateParameter (w.maximalIdeal.adicCompletion F)) :
    ((iutEmbedTateParameter hvw t).q : v.maximalIdeal.adicCompletion Kt) =
      iutEmbedCompletion hvw (t.q : w.maximalIdeal.adicCompletion F) :=
  Units.coe_map _ _

private lemma iutEisenstein_embed
    {F Kt : Type u} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
    [Algebra F Kt] {v : NumberField.FinitePlace Kt} {w : NumberField.FinitePlace F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (t : TateParameter (w.maximalIdeal.adicCompletion F)) (n : ℕ) :
    iutEmbedCompletion hvw (t.eisenstein n) =
      (iutEmbedTateParameter hvw t).eisenstein n := by
  unfold TateParameter.eisenstein
  rw [(t.eisenstein_summand_summable n).map_tsum (iutEmbedCompletion hvw)
    (iutContinuousEmbedCompletion hvw)]
  refine tsum_congr fun m => ?_
  simp only [map_div₀, map_mul, map_pow, map_natCast, map_sub, map_one,
    iutEmbedTateParameter_q_coe]

private lemma iutTateCurve_embed
    {F Kt : Type u} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
    [Algebra F Kt] {v : NumberField.FinitePlace Kt} {w : NumberField.FinitePlace F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (t : TateParameter (w.maximalIdeal.adicCompletion F)) :
    t.tateCurve.map (iutEmbedCompletion hvw) =
      (iutEmbedTateParameter hvw t).tateCurve := by
  ext <;> simp [WeierstrassCurve.map, TateParameter.tateCurve, TateParameter.a₄,
    TateParameter.a₆, iutEisenstein_embed, map_ofNat]

lemma iutTateJ_embed
    {F Kt : Type u} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
    [Algebra F Kt] {v : NumberField.FinitePlace Kt} {w : NumberField.FinitePlace F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (t : TateParameter (w.maximalIdeal.adicCompletion F)) :
    iutEmbedCompletion hvw t.tateJ = (iutEmbedTateParameter hvw t).tateJ := by
  rw [TateParameter.tateJ_def, TateParameter.tateJ_def, map_div₀, map_pow,
    ← WeierstrassCurve.map_c₄, ← WeierstrassCurve.map_Δ, iutTateCurve_embed]

lemma iutTateStructure_tateJ_eq
    {K : Type u} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    [Valuation.RankOne (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))]
    [CompleteSpace K] {E : WeierstrassCurve K}
    (S : JoshiTeich.ReferenceIut.TateStructure E) :
    S.t.tateJ = E.c₄ ^ 3 / E.Δ := by
  rw [TateParameter.tateJ_def, ← S.hC, WeierstrassCurve.variableChange_c₄,
    WeierstrassCurve.variableChange_Δ]
  have hu : ((S.C.u⁻¹ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  rw [mul_pow, ← pow_mul, show 4 * 3 = 12 from rfl]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hu)

lemma iutCurve_j_eq_div
    {F : Type u} [Field F] [NumberField F]
    (E : WeierstrassCurve F) [E.IsElliptic] :
    E.j = E.c₄ ^ 3 / E.Δ := by
  rw [WeierstrassCurve.j, div_eq_inv_mul]
  congr 1
  rw [← WeierstrassCurve.coe_Δ', ← Units.val_inv_eq_inv_val]

/-- Equality of Tate `j`-invariants determines the embedded q-parameter. -/
theorem iutTateParameter_q_eq_of_tateJ_eq
    {F Kt : Type u} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
    [Algebra F Kt] {v : NumberField.FinitePlace Kt} {w : NumberField.FinitePlace F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (t : TateParameter (w.maximalIdeal.adicCompletion F))
    (s : TateParameter (v.maximalIdeal.adicCompletion Kt))
    (hJ : (iutEmbedTateParameter hvw t).tateJ = s.tateJ) :
    (s.q : v.maximalIdeal.adicCompletion Kt) =
      iutEmbedCompletion hvw (t.q : w.maximalIdeal.adicCompletion F) := by
  have hParam := TateParameter.tateJ_injective
    (iutEmbedTateParameter hvw t) s
    (JoshiTeich.ReferenceIut.twelve_ne_zero v) hJ
  rw [← hParam, iutEmbedTateParameter_q_coe]

end

end JoshiTeich.Act1Scene1
