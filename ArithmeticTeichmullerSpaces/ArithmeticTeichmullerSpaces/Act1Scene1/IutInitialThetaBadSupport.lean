import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootAccounting
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.Basic
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PlaceUnder
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PlacesOver
import Mathlib.NumberTheory.RamificationInertia.Valuation

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open WeierstrassCurve
open scoped NumberField

universe u

/-!
source-id: IUT-COR312-INITIAL-THETA-BAD-SUPPORT
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/GlobalField.lean`,
`badPlacesOver`, `IsInitialThetaGlobalData.bad_odd`, and
`IsInitialThetaGlobalData.bad_multiplicative`; `refer/iut/Iut/Cor312/ThetaData/PlaceUnder.lean`,
`placeUnder`, `liesOver_placeUnder`, and `one_lt_valuation_j_of_mult`;
`refer/iut/Iut/Cor312/ThetaData/PlacesOver.lean`, `FinitePlace.exists_liesOver`;
`refer/iut/Iut/Tripod/CyclicTorsion.lean`, `EllipticCurveData.VBadOdd`.
fidelity: proves the actual IUT `VBad` is contained in a canonical odd
multiplicative support on `F_mod`, and that pulling this support to `F` gives
exactly all odd multiplicative places of the curve. It does not identify the
chosen `VBad` with that full support or with the paper's `V_p^oss`.
boundary: Scene1/Derived
-/

noncomputable section

private theorem iut_norm_emb_le_one_iff
    {F : Type u} [Field F] [NumberField F] (w : NumberField.FinitePlace F) (y : F) :
    ‖(NumberField.FinitePlace.embedding w.maximalIdeal y :
      JoshiTeich.ReferenceIut.localCompletion w)‖ ≤ 1 ↔
      w.maximalIdeal.valuation F y ≤ 1 := by
  rw [JoshiTeich.ReferenceIut.norm_le_one_iff_valued, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation']

/-- The odd-characteristic multiplicative places of the IUT base curve. -/
def IutOddMultiplicativeSupport
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) : Set (NumberField.FinitePlace D.F) :=
  {w | Odd (Arithmetic.residueChar w) ∧ JoshiTeich.ReferenceIut.HasMultiplicativeReductionAt D.E w}

/-- The canonical odd multiplicative support on the field of moduli, porting
`JoshiTeich.ReferenceIut.EllipticCurveData.VBadOdd`. -/
def IutOddMultiplicativeModSupport
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Set (NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :=
  {v | Odd (Arithmetic.residueChar v) ∧
    (∃ w : NumberField.FinitePlace D.F, JoshiTeich.ReferenceIut.FinitePlace.LiesOver w v) ∧
    ∀ w : NumberField.FinitePlace D.F, JoshiTeich.ReferenceIut.FinitePlace.LiesOver w v →
      JoshiTeich.ReferenceIut.HasMultiplicativeReductionAt D.E w}

private theorem iut_multiplicative_reduction_invariant_over_mod_place
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)}
    {w w' : NumberField.FinitePlace D.F}
    (hwv : JoshiTeich.ReferenceIut.FinitePlace.LiesOver w v)
    (hw'v : JoshiTeich.ReferenceIut.FinitePlace.LiesOver w' v)
    (hm : JoshiTeich.ReferenceIut.HasMultiplicativeReductionAt D.E w) :
    JoshiTeich.ReferenceIut.HasMultiplicativeReductionAt D.E w' := by
  let j₀ : ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) :=
    ⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩
  have valLeOneIff (x : NumberField.FinitePlace D.F)
      (hxv : JoshiTeich.ReferenceIut.FinitePlace.LiesOver x v) :
      x.maximalIdeal.valuation D.F D.E.j ≤ 1 ↔
        v.maximalIdeal.valuation _ j₀ ≤ 1 := by
    haveI : x.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hxv
    change x.maximalIdeal.valuation D.F (algebraMap _ _ j₀) ≤ 1 ↔ _
    rw [← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver
      D.F v.maximalIdeal x.maximalIdeal j₀]
    exact pow_le_one_iff_of_nonneg zero_le
      (Ideal.ramificationIdx_pos_of_isDedekindDomain' x.maximalIdeal.asIdeal
        v.maximalIdeal.ne_bot).ne'
  have multIffNotValLeOne (x : NumberField.FinitePlace D.F) :
      JoshiTeich.ReferenceIut.HasMultiplicativeReductionAt D.E x ↔
        ¬ x.maximalIdeal.valuation D.F D.E.j ≤ 1 := by
    constructor
    · intro hx
      exact not_le_of_gt (JoshiTeich.ReferenceIut.one_lt_valuation_j_of_mult D.E x hx)
    · intro hnot
      rcases D.global.stable_reduction x with hg | hm'
      · exfalso
        apply hnot
        obtain ⟨C, hC⟩ := hg
        haveI : ((C • D.E).baseChange (x.maximalIdeal.adicCompletion D.F)).HasGoodReduction
            (x.maximalIdeal.adicCompletionIntegers D.F) := hC
        have hΔ : ‖((C • D.E).baseChange
            (x.maximalIdeal.adicCompletion D.F)).Δ‖ = 1 :=
          (JoshiTeich.ReferenceIut.valuation_eq_one_iff x _).1 HasGoodReduction.goodReduction
        have hc₄ : ‖((C • D.E).baseChange
            (x.maximalIdeal.adicCompletion D.F)).c₄‖ ≤ 1 := JoshiTeich.ReferenceIut.norm_c₄_le_one _
        rw [JoshiTeich.ReferenceIut.baseChange_adicCompletion_eq, map_Δ] at hΔ
        rw [JoshiTeich.ReferenceIut.baseChange_adicCompletion_eq, map_c₄] at hc₄
        rw [← variableChange_j D.E C, ← iut_norm_emb_le_one_iff,
          JoshiTeich.ReferenceIut.j_eq_inv_Δ_mul, map_mul, map_inv₀, map_pow, norm_mul, norm_inv, norm_pow,
          hΔ, inv_one, one_mul]
        exact pow_le_one₀ (norm_nonneg _) hc₄
      · exact hm'
  have key (x : NumberField.FinitePlace D.F)
      (hxv : JoshiTeich.ReferenceIut.FinitePlace.LiesOver x v) :
      x.maximalIdeal.valuation D.F D.E.j ≤ 1 ↔
        v.maximalIdeal.valuation _ j₀ ≤ 1 :=
    valLeOneIff x hxv
  have hmult : ¬ w.maximalIdeal.valuation D.F D.E.j ≤ 1 :=
    (multIffNotValLeOne w).mp hm
  apply (multIffNotValLeOne w').mpr
  intro hw'le
  apply hmult
  exact (key w hwv).2 ((key w' hw'v).1 hw'le)

/-- Every odd multiplicative place of `F` lies over the canonical support on `F_mod`. -/
theorem mem_iutOddMultiplicativeModSupport_of_mem_support
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) {w : NumberField.FinitePlace D.F}
    (hw : w ∈ IutOddMultiplicativeSupport D) :
    JoshiTeich.ReferenceIut.placeUnder (k := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) w ∈
      IutOddMultiplicativeModSupport D := by
  rcases hw with ⟨hodd, hmult⟩
  have hwv : JoshiTeich.ReferenceIut.FinitePlace.LiesOver w
      (JoshiTeich.ReferenceIut.placeUnder (k := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) w) :=
    JoshiTeich.ReferenceIut.liesOver_placeUnder (k := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) w
  refine ⟨?_, ⟨w, hwv⟩, ?_⟩
  · rw [← Arithmetic.residueChar_eq_of_liesOver hwv]
    exact hodd
  · intro w' hw'v
    exact iut_multiplicative_reduction_invariant_over_mod_place D hwv hw'v hmult

/-- The IUT-selected `VBad` is contained in the canonical odd multiplicative support. -/
theorem iutInitialThetaVBad_subset_oddMultiplicativeModSupport
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    D.VBad ⊆ IutOddMultiplicativeModSupport D := by
  intro v hv
  obtain ⟨w, hwv⟩ := JoshiTeich.ReferenceIut.FinitePlace.exists_liesOver (K := D.F) v
  refine ⟨D.global.bad_odd v hv, ⟨w, hwv⟩, ?_⟩
  intro w' hw'v
  exact D.global.bad_multiplicative v hv w' hw'v

/-- Pulling the canonical mod-field support to `F` gives exactly all odd
multiplicative places of the actual IUT curve. -/
theorem iutOddMultiplicativeSupport_eq_badPlacesOver_modSupport
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    IutOddMultiplicativeSupport D =
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E (IutOddMultiplicativeModSupport D) := by
  ext w
  constructor
  · intro hw
    refine ⟨JoshiTeich.ReferenceIut.placeUnder (k := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) w,
      mem_iutOddMultiplicativeModSupport_of_mem_support D hw, ?_⟩
    exact JoshiTeich.ReferenceIut.liesOver_placeUnder (k := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) w
  · rintro ⟨v, hv, hwv⟩
    refine ⟨?_, hv.2.2 w hwv⟩
    rw [Arithmetic.residueChar_eq_of_liesOver hwv]
    exact hv.1

/-- The actual IUT q-pilot support lies in the odd multiplicative support. -/
theorem iutBadPlacesOver_subset_oddMultiplicativeSupport
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad ⊆ IutOddMultiplicativeSupport D := by
  intro w hw
  rcases hw with ⟨v, hv, hwv⟩
  refine ⟨?_, D.global.bad_multiplicative v hv w hwv⟩
  rw [Arithmetic.residueChar_eq_of_liesOver hwv]
  exact D.global.bad_odd v hv

end

end JoshiTeich.Act1Scene1
