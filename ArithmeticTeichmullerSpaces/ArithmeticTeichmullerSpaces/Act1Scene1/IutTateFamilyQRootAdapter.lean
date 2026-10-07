import ArithmeticTeichmullerSpaces.Act1Scene1.IutTorsionRationality
import ArithmeticTeichmullerSpaces.Act1Scene1.IutAdmissiblePrimeSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompletionSource
import Iut.Cor312.ThetaData.Basic
import Iut.Cor312.ThetaData.TateFamily

/-!
source-id: IUT-COR312-TATE-FAMILY-QROOT-ADAPTER
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/TateStructure.lean` and
`refer/iut/Iut/Cor312/ThetaData/TateFamily.lean`; the completion comparison proof is
ported from `refer/iut/Iut/Concrete/ThetaLocalConstruct/TateCompat.lean` and
`refer/iut/Iut/Concrete/ThetaLocalConstruct/EmbedCompletion.lean`.
fidelity: the actual IUT Tate parameter and uniformization is projected into the
group-theoretic quotient interface used by the q-root assembler. The
`InitialThetaData` constructor derives the bad-place certificate, torsion basis,
six-torsion condition, and positive odd prime from its actual fields. For the
canonical admissible-prime base source, equality with the embedded base-completion
parameter is proved from the IUT `j`-identity and Tate-parameter injectivity; the
generic source constructor still accepts that equality explicitly.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open WeierstrassCurve
open NumberField
open TateCurvesTheta
open scoped Classical Valued

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosed Fbar]
variable {Kt : IntermediateField F Fbar} [NumberField Kt]
variable {E : WeierstrassCurve F} [E.IsElliptic]
variable {ell : ℕ}

local instance (priority := 1100) instDecidableEqKt : DecidableEq ↥Kt :=
  fun a b => Classical.propDecidable (a = b)

/-- Project the actual IUT Tate structure into the quotient-uniformization
interface used by the q-root argument. -/
def IutTateQuotientUniformization.ofTateStructure
    {K : Type u} [Field K]
    [Valued K (WithZero (Multiplicative ℤ))]
    [Valuation.RankOne (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))]
    [CompleteSpace K]
    {E : WeierstrassCurve K} (S : Iut.TateStructure E) :
    IutTateQuotientUniformization K E.toAffine.Point :=
  { q := S.t.q
    q_norm_lt_one := S.t.norm_lt_one
    iso := S.iso }

private def iutEmbedTateParameter
    {F Kt : Type u} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
    [Algebra F Kt] {v : NumberField.FinitePlace Kt} {w : NumberField.FinitePlace F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (t : TateParameter (w.maximalIdeal.adicCompletion F)) :
    TateParameter (v.maximalIdeal.adicCompletion Kt) where
  q := Units.map (iutEmbedCompletion hvw).toMonoidHom t.q
  norm_lt_one := by
    rw [Units.coe_map]
    exact (iutEmbedCompletion_norm_lt_one_iff hvw (t.q : _)).2 t.norm_lt_one

private lemma iutEmbedTateParameter_q_coe
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
    t.tateCurve.map (iutEmbedCompletion hvw) = (iutEmbedTateParameter hvw t).tateCurve := by
  ext <;> simp [WeierstrassCurve.map, TateParameter.tateCurve, TateParameter.a₄,
    TateParameter.a₆, iutEisenstein_embed, map_ofNat]

private lemma iutTateJ_embed
    {F Kt : Type u} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
    [Algebra F Kt] {v : NumberField.FinitePlace Kt} {w : NumberField.FinitePlace F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (t : TateParameter (w.maximalIdeal.adicCompletion F)) :
    iutEmbedCompletion hvw t.tateJ = (iutEmbedTateParameter hvw t).tateJ := by
  rw [TateParameter.tateJ_def, TateParameter.tateJ_def, map_div₀, map_pow,
    ← WeierstrassCurve.map_c₄, ← WeierstrassCurve.map_Δ, iutTateCurve_embed]

private lemma iutTateStructure_tateJ_eq
    {K : Type u} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    [Valuation.RankOne (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))]
    [CompleteSpace K] {E : WeierstrassCurve K} (S : Iut.TateStructure E) :
    S.t.tateJ = E.c₄ ^ 3 / E.Δ := by
  rw [TateParameter.tateJ_def, ← S.hC, WeierstrassCurve.variableChange_c₄,
    WeierstrassCurve.variableChange_Δ]
  have hu : ((S.C.u⁻¹ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  rw [mul_pow, ← pow_mul, show 4 * 3 = 12 from rfl]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hu)

private lemma iutCurve_j_eq_div
    {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic] :
    E.j = E.c₄ ^ 3 / E.Δ := by
  rw [WeierstrassCurve.j, div_eq_inv_mul]
  congr 1
  rw [← WeierstrassCurve.coe_Δ', ← Units.val_inv_eq_inv_val]

private theorem iutTateFamily_q_eq_baseCompletion
    {AG : Iut.AnabelianGeometry.{u}} {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG)
    {v : NumberField.FinitePlace ↥D.prime.torsionField}
    {w : NumberField.FinitePlace D.F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (hBad : w ∈ Iut.badPlacesOver D.F D.E D.VBad)
    (hSBad : Iut.IsBadPlace D.E D.prime.torsionField D.VBad v) :
    ((D.tate.S v hSBad).t.q : v.maximalIdeal.adicCompletion ↥D.prime.torsionField) =
      iutEmbedCompletion hvw ((D.prime.tate w hBad).q : w.maximalIdeal.adicCompletion D.F) := by
  have hJ : (iutEmbedTateParameter hvw (D.prime.tate w hBad)).tateJ =
      (D.tate.S v hSBad).t.tateJ := by
    rw [← iutTateJ_embed, D.prime.tateJ_eq w hBad,
      iutEmbedCompletion_embedding hvw, iutTateStructure_tateJ_eq,
      iutCurve_j_eq_div]
    simp only [Iut.curveKw, Iut.curveK, WeierstrassCurve.map_c₄,
      WeierstrassCurve.map_Δ, map_div₀, map_pow]
  have hTateEq := TateParameter.tateJ_injective
    (iutEmbedTateParameter hvw (D.prime.tate w hBad)) (D.tate.S v hSBad).t
    (Iut.twelve_ne_zero v) hJ
  rw [← hTateEq, iutEmbedTateParameter_q_coe]

/-- Assemble the q-root source from the actual IUT Tate family. The proof that each
torsion-field place belongs to the IUT bad locus and the comparison of its Tate
parameter with the base completion parameter are retained as explicit inputs. -/
noncomputable def IutTorsionQRootSource.ofTateFamily
    (B : IutBaseQPilotSource F ell)
    (T : IutGlobalTorsionBasis (E.map (algebraMap F ↥Kt)).toAffine.Point ell)
    (VBad : Set (NumberField.FinitePlace ↥(Iut.fieldOfModuli F E)))
    (TF : Iut.TateFamily E Kt ell VBad)
    (hBad : ∀ w : iutBadPlacesOverFinset (k := F) (K := ↥Kt)
      B.badPlaces B.badPlaces_finite,
      Iut.IsBadPlace E Kt VBad w.1)
    (hsix : IutSixTorsionRational (F := F) (Fbar := Fbar) (E := E))
    (hEll : 0 < ell) (hodd : Odd ell)
    (hq : ∀ w : iutBadPlacesOverFinset (k := F) (K := ↥Kt)
      B.badPlaces B.badPlaces_finite,
      ((TF.S w.1 (hBad w)).t.q : w.1.maximalIdeal.adicCompletion ↥Kt) =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) w)
          (B.tateParameter (basePlaceOf (B := B) w))) :
    IutTorsionQRootSource F ↥Kt ell B := by
  exact IutTorsionQRootSource.ofOverBaseBadWithCanonicalCompletionMap_ofWeierstrassTorsion
    B T
    (fun w => IutTateQuotientUniformization.ofTateStructure (TF.S w.1 (hBad w)))
    hsix hEll hodd hq

/-- Derive the local bad-place condition from the actual initial Theta-data carrier and
the base q-pilot carrier equality. -/
theorem iutInitialThetaTateFamily_badPlace
    {AG : Iut.AnabelianGeometry.{u}}
    {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG)
    (B : IutBaseQPilotSource D.F D.prime.ℓ)
    (hPlaces : B.badPlaces = Iut.badPlacesOver D.F D.E D.VBad)
    (w : iutBadPlacesOverFinset (k := D.F) (K := ↥D.prime.torsionField)
      B.badPlaces B.badPlaces_finite) :
    Iut.IsBadPlace D.E D.prime.torsionField D.VBad w.1 := by
  have hbase : (IutTorsionQRootSource.basePlaceOf (B := B) w).1 ∈ B.badPlaces :=
    IutBaseQPilotSource.mem_badPlaces B
      (IutTorsionQRootSource.basePlaceOf (B := B) w)
  rw [hPlaces] at hbase
  rcases hbase with ⟨v, hv, hvbase⟩
  letI : Algebra ↥(Iut.fieldOfModuli D.F D.E) ↥D.prime.torsionField :=
    (Iut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem
  have hfieldMap (x : ↥(Iut.fieldOfModuli D.F D.E)) :
      algebraMap ↥(Iut.fieldOfModuli D.F D.E) ↥D.prime.torsionField x =
        algebraMap D.F ↥D.prime.torsionField
          (algebraMap ↥(Iut.fieldOfModuli D.F D.E) D.F x) := by
    rfl
  have hfieldHom :
      algebraMap ↥(Iut.fieldOfModuli D.F D.E) ↥D.prime.torsionField =
        (algebraMap D.F ↥D.prime.torsionField).comp
          (algebraMap ↥(Iut.fieldOfModuli D.F D.E) D.F) :=
    RingHom.ext hfieldMap
  letI : IsScalarTower ↥(Iut.fieldOfModuli D.F D.E) D.F
      ↥D.prime.torsionField :=
    IsScalarTower.of_algebraMap_eq' hfieldHom
  letI : IsScalarTower (𝓞 ↥(Iut.fieldOfModuli D.F D.E)) (𝓞 D.F)
      (𝓞 ↥D.prime.torsionField) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      apply RingOfIntegers.coe_injective
      exact RingHom.congr_fun hfieldHom x)
  haveI : w.1.maximalIdeal.asIdeal.LiesOver
      (IutTorsionQRootSource.basePlaceOf (B := B) w).1.maximalIdeal.asIdeal :=
    IutTorsionQRootSource.basePlaceOf_liesOver (B := B) w
  haveI : (IutTorsionQRootSource.basePlaceOf (B := B) w).1.maximalIdeal.asIdeal.LiesOver
      v.maximalIdeal.asIdeal := hvbase
  exact ⟨v, hv, ⟨(Ideal.LiesOver.trans w.1.maximalIdeal.asIdeal
    (IutTorsionQRootSource.basePlaceOf (B := B) w).1.maximalIdeal.asIdeal
    v.maximalIdeal.asIdeal).over⟩⟩

/-- Identify the actual Tate-family parameter with the image of the admissible-prime
parameter. This is the reference project's `TateStructure.t_q_eq_embedCompletion`,
transported to the completion-map definition used by Scene1. -/
theorem iutInitialThetaTateFamily_q_eq_baseParameter
    {AG : Iut.AnabelianGeometry.{u}}
    {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG)
    (B : IutBaseQPilotSource D.F D.prime.ℓ)
    (hPlaces : B.badPlaces = Iut.badPlacesOver D.F D.E D.VBad)
    (hParameter : ∀ w : B.badFinset,
      B.tateParameter w =
        (D.prime.tate w.1 (by
          have hw := B.mem_badPlaces w
          rw [hPlaces] at hw
          exact hw)).q)
    (v : iutBadPlacesOverFinset (k := D.F) (K := ↥D.prime.torsionField)
      B.badPlaces B.badPlaces_finite) :
    ((D.tate.S v.1 (iutInitialThetaTateFamily_badPlace D B hPlaces v)).t.q :
      v.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) =
      iutEmbedCompletion (IutTorsionQRootSource.basePlaceOf_liesOver (B := B) v)
        (B.tateParameter (IutTorsionQRootSource.basePlaceOf (B := B) v)) := by
  let w := IutTorsionQRootSource.basePlaceOf (B := B) v
  have hw : w.1 ∈ Iut.badPlacesOver D.F D.E D.VBad := by
    rw [← hPlaces]
    exact B.mem_badPlaces w
  have hBad := iutInitialThetaTateFamily_badPlace D B hPlaces v
  have hvw := IutTorsionQRootSource.basePlaceOf_liesOver (B := B) v
  have hq := iutTateFamily_q_eq_baseCompletion D hvw hw hBad
  calc
    _ = iutEmbedCompletion hvw ((D.prime.tate w.1 hw).q :
        w.1.maximalIdeal.adicCompletion D.F) := hq
    _ = iutEmbedCompletion hvw (B.tateParameter w) := by
      rw [hParameter w]

/-- Assemble q-root data from the real `InitialThetaData` and `TateFamily` fields.
The equality between each local Tate parameter and the base-completion parameter remains
an explicit source condition. -/
noncomputable def IutTorsionQRootSource.ofInitialThetaData
    {AG : Iut.AnabelianGeometry.{u}}
    {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG)
    (B : IutBaseQPilotSource D.F D.prime.ℓ)
    (hPlaces : B.badPlaces = Iut.badPlacesOver D.F D.E D.VBad)
    (hq : ∀ w : iutBadPlacesOverFinset (k := D.F) (K := ↥D.prime.torsionField)
      B.badPlaces B.badPlaces_finite,
      ((D.tate.S w.1 (iutInitialThetaTateFamily_badPlace D B hPlaces w)).t.q :
        w.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) =
        iutEmbedCompletion (IutTorsionQRootSource.basePlaceOf_liesOver (B := B) w)
          (B.tateParameter (IutTorsionQRootSource.basePlaceOf (B := B) w))) :
    IutTorsionQRootSource D.F ↥D.prime.torsionField D.prime.ℓ B := by
  let P := IutAdmissiblePrimeTorsionData.ofAdmissiblePrimeData
    D.prime D.isAlgClosure
  letI : IsAlgClosed D.Fbar := D.isAlgClosure.isAlgClosed
  have hsix : IutSixTorsionRational (F := D.F) (Fbar := D.Fbar) (E := D.E) := by
    have hcurve : Affine.baseChange D.E D.Fbar =
        (D.E.map (algebraMap D.F D.Fbar)).toAffine := rfl
    cases hcurve
    change ∀ P ∈ iutTorsion
      ((D.E.map (algebraMap D.F D.Fbar)).toAffine.Point) 6,
      P ∈ (iutWeierstrassPointMap (E := D.E) (algebraMap D.F D.Fbar)).range
    exact D.global.six_torsion_rational
  have hfield := IutAdmissiblePrimeTorsionData.torsionField_eq_admissiblePrime
    D.prime D.isAlgClosure
  have T : IutGlobalTorsionBasis
      (D.E.map (algebraMap D.F ↥D.prime.torsionField)).toAffine.Point D.prime.ℓ := by
    rw [← hfield]
    exact P.toGlobalTorsionBasis
  exact IutTorsionQRootSource.ofTateFamily B T D.VBad D.tate
    (fun w => iutInitialThetaTateFamily_badPlace D B hPlaces w)
    hsix P.ell_pos P.ell_odd hq

/-- Assemble q-root data from `InitialThetaData` and the bad-place finiteness field
of its IUT q-pilot input. The base parameter is fixed to `D.prime.tate`; the local
comparison is proved from the actual `TateFamily`. -/
noncomputable def IutTorsionQRootSource.ofInitialThetaDataOfQPilotBadPlaceFiniteness
    {AG : Iut.AnabelianGeometry.{u}}
    {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG)
    (hBadFinite : (Iut.badPlacesOver D.F D.E D.VBad).Finite) :
    IutTorsionQRootSource D.F ↥D.prime.torsionField D.prime.ℓ
      (IutBaseQPilotSource.ofAdmissiblePrimeData D.prime.ℓ D.prime hBadFinite) := by
  let B := IutBaseQPilotSource.ofAdmissiblePrimeData D.prime.ℓ D.prime hBadFinite
  have hPlaces : B.badPlaces = Iut.badPlacesOver D.F D.E D.VBad := rfl
  have hParameter : ∀ w : B.badFinset,
      B.tateParameter w =
        (D.prime.tate w.1 (by
          have hw := B.mem_badPlaces w
          rw [hPlaces] at hw
          exact hw)).q := by
    intro w
    rfl
  exact IutTorsionQRootSource.ofInitialThetaData D B hPlaces
    (fun w => iutInitialThetaTateFamily_q_eq_baseParameter D B hPlaces hParameter w)

end

end JoshiTeich.Act1Scene1
