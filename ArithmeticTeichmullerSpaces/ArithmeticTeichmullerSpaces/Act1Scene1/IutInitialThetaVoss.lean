import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTateFamily
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOddSupportQParameter
import ArithmeticTeichmullerSpaces.Act1Scene1.IutPlacesOver

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField TateCurvesTheta WeierstrassCurve
open scoped NumberField Valued

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-VOSS
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/LocalConditions.lean`,
`ValuationSection.sectFin` and `sectFin_liesOver`; `refer/iut/Iut/Tripod/CyclicTorsion.lean`,
`EllipticCurveData.VBadOdd`; `refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`,
`tateFamilyOfTorsion`; JoshiTeich, *Arithmetic Teichmuller Spaces III*,
`ss:theta-data-fixing2` and `ss:val-sets-defn`.
fidelity: characterizes the actual section image intersected with odd places carrying
the actual local Tate uniformization as the image of the complete odd multiplicative
moduli support, and proves finiteness of this section image and its Voss intersection.
The Tate-structure witness is the formal local uniformization criterion
for the paper's odd semistable locus. This does not identify an independently supplied
Scene1 link carrier or prove q-sum accounting.
boundary: Scene1/Derived
-/

private theorem iutVoss_norm_embedding_le_one_iff
    {F : Type u} [Field F] [NumberField F] (w : NumberField.FinitePlace F) (x : F) :
    ‖(NumberField.FinitePlace.embedding w.maximalIdeal x :
      JoshiTeich.ReferenceIut.localCompletion w)‖ ≤ 1 ↔
      w.maximalIdeal.valuation F x ≤ 1 := by
  rw [JoshiTeich.ReferenceIut.norm_le_one_iff_valued, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation']

private theorem iutVoss_curve_j_eq_div_of_field
    {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic] :
    E.j = E.c₄ ^ 3 / E.Δ := by
  rw [WeierstrassCurve.j, div_eq_inv_mul]
  congr 1
  rw [← WeierstrassCurve.coe_Δ', ← Units.val_inv_eq_inv_val]

private lemma iutVoss_tateJ_eq
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

private theorem iutVoss_curveKw_j_eq_embedding
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : NumberField.FinitePlace ↥D.prime.torsionField) :
    (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField w).j =
      NumberField.FinitePlace.embedding w.maximalIdeal
        (algebraMap D.F ↥D.prime.torsionField D.E.j) := by
  rw [iutVoss_curve_j_eq_div_of_field
      (E := JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField w),
    iutVoss_curve_j_eq_div_of_field (E := D.E)]
  simp only [JoshiTeich.ReferenceIut.curveKw, JoshiTeich.ReferenceIut.curveK,
    WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ, map_div₀, map_pow]

private theorem iutVoss_algebraModK_eq_canonical
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    D.algebraModK =
      (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem := by
  apply Algebra.algebra_ext
  intro x
  apply Subtype.ext
  calc
    ((D.algebraModK.algebraMap x : ↥D.prime.torsionField) : D.Fbar) =
        ((algebraMap D.F ↥D.prime.torsionField
          (algebraMap (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) D.F x) :
            ↥D.prime.torsionField) : D.Fbar) := by
      exact congrArg Subtype.val
        (@IsScalarTower.algebraMap_apply
          (↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) D.F
          ↥D.prime.torsionField _ _ _ _ _ D.algebraModK D.towerModK x)
    _ = ((JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem.algebraMap x :
        ↥D.prime.torsionField) := rfl

private theorem iutVoss_section_liesOver_canonical
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :
    @JoshiTeich.ReferenceIut.FinitePlace.LiesOver
      _ _ _ _ _ _
      (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem
      (iutInitialThetaFinitePlaceSection D v) v :=
  iutVoss_algebraModK_eq_canonical D ▸
    iutInitialThetaFinitePlaceSection_liesOver D v

/-- The odd semistable section locus, expressed through its local Tate uniformizations. -/
def iutInitialThetaOddTateSectionPlaces
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Set (NumberField.FinitePlace ↥D.prime.torsionField) :=
  {w | ∃ v, iutInitialThetaFinitePlaceSection D v = w ∧
    Odd (Arithmetic.residueChar w) ∧
    Nonempty (JoshiTeich.ReferenceIut.TateStructure
      (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField w))}

/-- The representative set selected by the actual `InitialThetaData` section. -/
noncomputable def iutInitialThetaSectionRepresentatives
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Set (NumberField.FinitePlace ↥D.prime.torsionField) :=
  Set.range (iutInitialThetaFinitePlaceSection D)

/-- The formal local Tate criterion used here for odd semistable places of `L'`. -/
def iutInitialThetaOddSemistablePlaces
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Set (NumberField.FinitePlace ↥D.prime.torsionField) :=
  {w | Odd (Arithmetic.residueChar w) ∧
    Nonempty (JoshiTeich.ReferenceIut.TateStructure
      (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField w))}

/-- The paper's `underline V^oss` intersection for the concrete representatives
selected by `InitialThetaData`. -/
def iutInitialThetaSectionVoss
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    Set (NumberField.FinitePlace ↥D.prime.torsionField) :=
  iutInitialThetaSectionRepresentatives D ∩ iutInitialThetaOddSemistablePlaces D

/-- The selected odd Tate locus is exactly the section-image/odd-semistable
intersection, with the section choice supplied by `InitialThetaData`. -/
theorem iutInitialThetaOddTateSectionPlaces_eq_sectionVoss
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaOddTateSectionPlaces D = iutInitialThetaSectionVoss D := by
  ext w
  simp [iutInitialThetaOddTateSectionPlaces,
    iutInitialThetaSectionVoss,
    iutInitialThetaSectionRepresentatives,
    iutInitialThetaOddSemistablePlaces]

/-- On the actual IUT section, odd Tate places are exactly the representatives of the
complete odd multiplicative support on the field of moduli. -/
theorem iutInitialThetaOddTateSectionPlaces_eq_selectedSupport
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaOddTateSectionPlaces D =
      iutInitialThetaOddMultiplicativeSelectedPlaces D := by
  classical
  ext w
  constructor
  · rintro ⟨v, rfl, hwOdd, ⟨S⟩⟩
    let M := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)
    let K := ↥D.prime.torsionField
    letI : Algebra ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) K :=
      (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem
    have hfieldMap (x : ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :
        algebraMap ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) K x =
          algebraMap D.F K
            (algebraMap ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) D.F x) := by
      rfl
    have hfieldHom :
        algebraMap ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) K =
          (algebraMap D.F K).comp
            (algebraMap ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) D.F) :=
      RingHom.ext hfieldMap
    letI : IsScalarTower ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) D.F K :=
      IsScalarTower.of_algebraMap_eq' hfieldHom
    letI : IsScalarTower (𝓞 ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
        (𝓞 D.F) (𝓞 K) :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
        apply RingOfIntegers.coe_injective
        exact RingHom.congr_fun hfieldHom x)
    have hOver : JoshiTeich.ReferenceIut.FinitePlace.LiesOver
        (iutInitialThetaFinitePlaceSection D v) v :=
      iutVoss_section_liesOver_canonical D v
    let j₀ : M := ⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩
    have hmap : algebraMap M K j₀ = algebraMap D.F K D.E.j := by
      rw [hfieldHom]
      rfl
    have hnorm : 1 < ‖NumberField.FinitePlace.embedding
        (iutInitialThetaFinitePlaceSection D v).maximalIdeal
        (algebraMap D.F K D.E.j)‖ := by
      rw [← iutVoss_curveKw_j_eq_embedding D (iutInitialThetaFinitePlaceSection D v),
        iutVoss_curve_j_eq_div_of_field
          (E := JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField
            (iutInitialThetaFinitePlaceSection D v)),
        ← iutVoss_tateJ_eq S]
      exact S.t.one_lt_norm_tateJ
        (JoshiTeich.ReferenceIut.twelve_ne_zero (iutInitialThetaFinitePlaceSection D v))
    have hvalK : ¬ (iutInitialThetaFinitePlaceSection D v).maximalIdeal.valuation K
        (algebraMap D.F K D.E.j) ≤ 1 := by
      intro hle
      exact (not_le_of_gt hnorm)
        ((iutVoss_norm_embedding_le_one_iff _ _).2 hle)
    have hvalLeOneIff :
        (iutInitialThetaFinitePlaceSection D v).maximalIdeal.valuation K
            (algebraMap M K j₀) ≤ 1 ↔ v.maximalIdeal.valuation M j₀ ≤ 1 := by
      haveI : (iutInitialThetaFinitePlaceSection D v).maximalIdeal.asIdeal.LiesOver
          v.maximalIdeal.asIdeal := hOver
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver
        K v.maximalIdeal (iutInitialThetaFinitePlaceSection D v).maximalIdeal j₀]
      exact pow_le_one_iff_of_nonneg zero_le
        (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
          (iutInitialThetaFinitePlaceSection D v).maximalIdeal.asIdeal
          v.maximalIdeal.ne_bot)
    have hvalM : ¬ v.maximalIdeal.valuation M j₀ ≤ 1 := by
      intro hle
      apply hvalK
      rw [← hmap]
      exact hvalLeOneIff.mpr hle
    let x := iutPlaceUnder (F := D.F) (Kt := K)
      (iutInitialThetaFinitePlaceSection D v)
    have hwx : JoshiTeich.ReferenceIut.FinitePlace.LiesOver
        (iutInitialThetaFinitePlaceSection D v) x :=
      iutPlaceUnder_liesOver (F := D.F) (Kt := K)
        (iutInitialThetaFinitePlaceSection D v)
    haveI : (iutInitialThetaFinitePlaceSection D v).maximalIdeal.asIdeal.LiesOver
        v.maximalIdeal.asIdeal := hOver
    haveI : (iutInitialThetaFinitePlaceSection D v).maximalIdeal.asIdeal.LiesOver
        x.maximalIdeal.asIdeal := hwx
    have hxv : x.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal :=
      Ideal.LiesOver.tower_bot (iutInitialThetaFinitePlaceSection D v).maximalIdeal.asIdeal
        x.maximalIdeal.asIdeal v.maximalIdeal.asIdeal
    have hvalFLeOneIff (x' : NumberField.FinitePlace D.F)
        (hx'v : JoshiTeich.ReferenceIut.FinitePlace.LiesOver x' v) :
        x'.maximalIdeal.valuation D.F D.E.j ≤ 1 ↔
          v.maximalIdeal.valuation M j₀ ≤ 1 := by
      haveI : x'.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hx'v
      change x'.maximalIdeal.valuation D.F (algebraMap M D.F j₀) ≤ 1 ↔ _
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver
        D.F v.maximalIdeal x'.maximalIdeal j₀]
      exact pow_le_one_iff_of_nonneg zero_le
        (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
          x'.maximalIdeal.asIdeal v.maximalIdeal.ne_bot)
    have hvOdd : Odd (Arithmetic.residueChar v) :=
      (Arithmetic.residueChar_prime v).odd_of_ne_two (by
        rw [← Arithmetic.residueChar_eq_of_liesOver hOver]
        intro htwo
        rcases hwOdd with ⟨k, hk⟩
        rw [htwo] at hk
        omega)
    have hSupport : v ∈ IutOddMultiplicativeModSupport D := by
      refine ⟨hvOdd, ⟨x, hxv⟩, ?_⟩
      intro x' hx'v
      apply (iutInitialThetaHasMultiplicativeReduction_iff_not_jValLEOne D x').mpr
      intro hle
      apply hvalM
      exact (hvalFLeOneIff x' hx'v).mp hle
    have hvPort : v ∈ iutVBadOddModSupportPort D := by
      rw [← iutInitialThetaOddMultiplicativeModSupport_eq_VBadOdd D]
      exact hSupport
    exact ⟨v, hvPort, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v, rfl, ?_, ?_⟩
    · letI : Algebra ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)
        ↥D.prime.torsionField :=
        (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem
      rw [Arithmetic.residueChar_eq_of_liesOver
        (iutVoss_section_liesOver_canonical D v)]
      exact (Arithmetic.residueChar_prime v).odd_of_ne_two hv.1
    · exact ⟨iutInitialThetaFinitePlaceSection_tateStructure D v hv⟩

/-! The concrete section/Voss carrier is finite because its source support is finite.
This is an actual carrier fact; it does not identify the carrier with the paper's
global place set or supply paper representative multiplicities. -/

theorem iutInitialThetaOddMultiplicativeSelectedPlaces_finite
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (iutInitialThetaOddMultiplicativeSelectedPlaces D).Finite := by
  exact (iutInitialThetaOddModSupport_finite D).image _

theorem iutInitialThetaSectionVoss_finite
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (iutInitialThetaSectionVoss D).Finite := by
  rw [← iutInitialThetaOddTateSectionPlaces_eq_sectionVoss D,
    iutInitialThetaOddTateSectionPlaces_eq_selectedSupport D]
  exact iutInitialThetaOddMultiplicativeSelectedPlaces_finite D

end

end JoshiTeich.Act1Scene1
