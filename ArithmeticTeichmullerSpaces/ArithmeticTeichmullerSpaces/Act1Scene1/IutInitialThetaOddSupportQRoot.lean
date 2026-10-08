import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOddSupportQParameter
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBadSupport
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadOddPort

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open IsDedekindDomain.HeightOneSpectrum
open WeierstrassCurve
open NumberField TateCurvesTheta
open scoped Classical NumberField Valued

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-ODD-SUPPORT-QROOT
source: `iut`: `refer/iut/Iut/Tripod/CyclicTorsion.lean`,
`EllipticCurveData.VBadOdd`; `refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`,
`tateFamilyOfTorsion`; `refer/iut/Iut/Concrete/ThetaLocalConstruct/TateCompat.lean`,
`TateStructure.t_q_eq_embedCompletion`; and the q-root construction ported from
`refer/iut/Iut/Concrete/ThetaLocalConstruct/TateTorsion.lean`.
fidelity: constructs actual base-completion Tate parameters on every odd
multiplicative place of the curve, identifies their images with the actual
torsion-field Tate family, and assembles a q-root source over the complete support.
This carrier has no proved `q_order_coprime` condition and is not identified with
the paper's `underline V^oss` or the Scene1 link carrier.
boundary: Scene1/Derived
-/

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

local instance (priority := 1100) iutInitialThetaOddSupport_instDecidableEqTorsionField
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    DecidableEq ↥D.prime.torsionField :=
  fun a b => Classical.propDecidable (a = b)

private theorem iut_norm_embedding_le_one_iff
    {F : Type u} [Field F] [NumberField F]
    (w : NumberField.FinitePlace F) (x : F) :
    ‖(NumberField.FinitePlace.embedding w.maximalIdeal x :
      JoshiTeich.ReferenceIut.localCompletion w)‖ ≤ 1 ↔
      w.maximalIdeal.valuation F x ≤ 1 := by
  rw [JoshiTeich.ReferenceIut.norm_le_one_iff_valued,
    FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']

private theorem iutCurve_j_eq_div_of_field
    {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic] :
    E.j = E.c₄ ^ 3 / E.Δ := by
  rw [WeierstrassCurve.j, div_eq_inv_mul]
  congr 1
  rw [← WeierstrassCurve.coe_Δ', ← Units.val_inv_eq_inv_val]

/-- A multiplicative-reduction place has `j`-norm greater than one in its completion. -/
theorem iutInitialThetaOddSupportBase_j_norm_gt_one
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : NumberField.FinitePlace D.F)
    (hw : w ∈ IutOddMultiplicativeSupport D) :
    1 < ‖(NumberField.FinitePlace.embedding w.maximalIdeal D.E.j :
      JoshiTeich.ReferenceIut.localCompletion w)‖ := by
  rcases hw with ⟨_, hmult⟩
  have hval := JoshiTeich.ReferenceIut.one_lt_valuation_j_of_mult D.E w hmult
  apply lt_of_not_ge
  intro hnorm
  exact (not_le_of_gt hval)
    ((iut_norm_embedding_le_one_iff w D.E.j).mp hnorm)

noncomputable def iutInitialThetaOddSupportBaseTateParameterAtCurvePlace
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : NumberField.FinitePlace D.F)
    (hw : w ∈ IutOddMultiplicativeSupport D) :
    TateParameter (w.maximalIdeal.adicCompletion D.F) :=
  Classical.choose (TateParameter.exists_tateParameter_tateJ_eq
    (JoshiTeich.ReferenceIut.twelve_ne_zero w)
    (iutInitialThetaOddSupportBase_j_norm_gt_one D w hw))

theorem iutInitialThetaOddSupportBaseTateParameterAtCurvePlace_tateJ_eq
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : NumberField.FinitePlace D.F)
    (hw : w ∈ IutOddMultiplicativeSupport D) :
    (iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D w hw).tateJ =
      NumberField.FinitePlace.embedding w.maximalIdeal D.E.j :=
  Classical.choose_spec (TateParameter.exists_tateParameter_tateJ_eq
    (JoshiTeich.ReferenceIut.twelve_ne_zero w)
    (iutInitialThetaOddSupportBase_j_norm_gt_one D w hw))

theorem iutInitialThetaOddMultiplicativeSupport_finite
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (IutOddMultiplicativeSupport D).Finite := by
  rw [iutOddMultiplicativeSupport_eq_badPlacesOver_modSupport]
  apply iutBadPlacesOver_finite
  rw [iutInitialThetaOddMultiplicativeModSupport_eq_VBadOdd D]
  exact iutInitialThetaOddModSupport_finite D

/-- The completion-valued base q source on the full odd multiplicative support. -/
noncomputable def iutInitialThetaOddSupportBaseQPilotSource
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    IutBaseQPilotSource D.F D.prime.ℓ := by
  let hfinite := iutInitialThetaOddMultiplicativeSupport_finite D
  refine
    { badPlaces := IutOddMultiplicativeSupport D
      badFinset := hfinite.toFinset
      badFinset_spec := hfinite.coe_toFinset
      weight := Arithmetic.qPilotWeight
      weight_eq_qPilotWeight := fun _ => rfl
      tateParameter := fun w =>
        (iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D w.1
          (hfinite.mem_toFinset.mp w.2)).q
      tateParameter_ne_zero := ?_
      tateParameter_norm_lt_one := ?_ }
  · intro w
    exact (iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D w.1
      (hfinite.mem_toFinset.mp w.2)).q.ne_zero
  · intro w
    exact (iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D w.1
      (hfinite.mem_toFinset.mp w.2)).norm_lt_one

theorem iutInitialThetaOddSupportBaseQPilotSource_tateJ_eq
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
    (iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D w.1
      ((iutInitialThetaOddSupportBaseQPilotSource D).mem_badPlaces w)).tateJ =
      NumberField.FinitePlace.embedding w.1.maximalIdeal D.E.j :=
  iutInitialThetaOddSupportBaseTateParameterAtCurvePlace_tateJ_eq D w.1
    ((iutInitialThetaOddSupportBaseQPilotSource D).mem_badPlaces w)

private theorem iutInitialThetaOddSupport_badPlaces_eq_fullModuliSupport
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (iutInitialThetaOddSupportBaseQPilotSource D).badPlaces =
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E
      (iutVBadOddModSupportPort D) := by
  change IutOddMultiplicativeSupport D =
    JoshiTeich.ReferenceIut.badPlacesOver D.F D.E
      (iutVBadOddModSupportPort D)
  rw [iutOddMultiplicativeSupport_eq_badPlacesOver_modSupport,
    iutInitialThetaOddMultiplicativeModSupport_eq_VBadOdd]

private theorem iutInitialThetaOddSupportTateFamily_badPlace
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (B : IutBaseQPilotSource D.F D.prime.ℓ)
    {VBad : Set (NumberField.FinitePlace
      ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))}
    (hPlaces : B.badPlaces = JoshiTeich.ReferenceIut.badPlacesOver D.F D.E VBad)
    (w : iutBadPlacesOverFinset (k := D.F) (K := ↥D.prime.torsionField)
      B.badPlaces B.badPlaces_finite) :
    JoshiTeich.ReferenceIut.IsBadPlace D.E D.prime.torsionField VBad w.1 := by
  have hbase : (IutTorsionQRootSource.basePlaceOf (B := B) w).1 ∈ B.badPlaces :=
    IutBaseQPilotSource.mem_badPlaces B
      (IutTorsionQRootSource.basePlaceOf (B := B) w)
  rw [hPlaces] at hbase
  rcases hbase with ⟨v, hv, hvbase⟩
  letI : Algebra ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) ↥D.prime.torsionField :=
    (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem
  have hfieldMap (x : ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :
      algebraMap ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) ↥D.prime.torsionField x =
        algebraMap D.F ↥D.prime.torsionField
          (algebraMap ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) D.F x) := by
    rfl
  have hfieldHom :
      algebraMap ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) ↥D.prime.torsionField =
        (algebraMap D.F ↥D.prime.torsionField).comp
          (algebraMap ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) D.F) :=
    RingHom.ext hfieldMap
  letI : IsScalarTower ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) D.F
      ↥D.prime.torsionField :=
    IsScalarTower.of_algebraMap_eq' hfieldHom
  letI : IsScalarTower (𝓞 ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) (𝓞 D.F)
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

/-- The actual `TateFamily` q parameter is the image of the base parameter at
every place over the full odd multiplicative support. -/
theorem iutInitialThetaOddSupportTateFamily_q_eq_baseParameter
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : iutBadPlacesOverFinset (k := D.F) (K := ↥D.prime.torsionField)
      (iutInitialThetaOddSupportBaseQPilotSource D).badPlaces
      (iutInitialThetaOddSupportBaseQPilotSource D).badPlaces_finite) :
    (((iutInitialThetaTateFamilyOfTorsion D).S w.1
      (iutInitialThetaOddSupportTateFamily_badPlace D
        (iutInitialThetaOddSupportBaseQPilotSource D)
        (iutInitialThetaOddSupport_badPlaces_eq_fullModuliSupport D) w)).t.q :
      w.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) =
      iutEmbedCompletion (IutTorsionQRootSource.basePlaceOf_liesOver
        (B := iutInitialThetaOddSupportBaseQPilotSource D) w)
        ((iutInitialThetaOddSupportBaseQPilotSource D).tateParameter
          (IutTorsionQRootSource.basePlaceOf
            (B := iutInitialThetaOddSupportBaseQPilotSource D) w)) := by
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let b := IutTorsionQRootSource.basePlaceOf (B := B) w
  let hvw := IutTorsionQRootSource.basePlaceOf_liesOver (B := B) w
  let t := iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D b.1
    (B.mem_badPlaces b)
  let hBad := iutInitialThetaOddSupportTateFamily_badPlace D B
    (iutInitialThetaOddSupport_badPlaces_eq_fullModuliSupport D) w
  let S := (iutInitialThetaTateFamilyOfTorsion D).S w.1 hBad
  have hJ : (iutEmbedTateParameter hvw t).tateJ = S.t.tateJ := by
    calc
      (iutEmbedTateParameter hvw t).tateJ = iutEmbedCompletion hvw t.tateJ :=
        (iutTateJ_embed hvw t).symm
      _ = NumberField.FinitePlace.embedding w.1.maximalIdeal
          (algebraMap D.F ↥D.prime.torsionField D.E.j) := by
        rw [iutInitialThetaOddSupportBaseTateParameterAtCurvePlace_tateJ_eq D b.1
          (B.mem_badPlaces b), iutEmbedCompletion_embedding hvw]
      _ = (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField w.1).j := by
        rw [iutCurve_j_eq_div_of_field (E := D.E),
          iutCurve_j_eq_div_of_field
            (E := JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField w.1)]
        simp only [JoshiTeich.ReferenceIut.curveKw,
          JoshiTeich.ReferenceIut.curveK, WeierstrassCurve.map_c₄,
          WeierstrassCurve.map_Δ, map_div₀, map_pow]
      _ = S.t.tateJ := by
        calc
          (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField w.1).j =
              (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField w.1).c₄ ^ 3 /
                (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField w.1).Δ :=
            iutCurve_j_eq_div_of_field _
          _ = S.t.tateJ := (iutTateStructure_tateJ_eq S).symm
  exact iutTateParameter_q_eq_of_tateJ_eq hvw t S.t hJ

/-- Assemble q roots from actual initial theta data on every torsion-field place
above the full odd multiplicative support. This does not add the IUT q-order
coprimality condition or identify the carrier with the Scene1 link. -/
noncomputable def iutInitialThetaOddSupportTorsionQRootSource
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    IutTorsionQRootSource D.F ↥D.prime.torsionField D.prime.ℓ
      (iutInitialThetaOddSupportBaseQPilotSource D) := by
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let P := IutAdmissiblePrimeTorsionData.ofAdmissiblePrimeData
    D.prime D.isAlgClosure
  letI : IsAlgClosed D.Fbar := D.isAlgClosure.isAlgClosed
  have hsix : IutSixTorsionRational (F := D.F) (Fbar := D.Fbar) (E := D.E) := by
    have hcurve : Affine.baseChange D.E D.Fbar =
        (D.E.map (algebraMap D.F D.Fbar)).toAffine := rfl
    cases hcurve
    change ∀ Q ∈ iutTorsion
      ((D.E.map (algebraMap D.F D.Fbar)).toAffine.Point) 6,
      Q ∈ (iutWeierstrassPointMap (E := D.E) (algebraMap D.F D.Fbar)).range
    exact D.global.six_torsion_rational
  have hfield : P.representationData.torsionField = D.prime.torsionField :=
    IutAdmissiblePrimeTorsionData.torsionField_eq_admissiblePrime
      D.prime D.isAlgClosure
  have T : IutGlobalTorsionBasis
      (D.E.map (algebraMap D.F ↥D.prime.torsionField)).toAffine.Point D.prime.ℓ := by
    let basisType := fun K : IntermediateField D.F D.Fbar =>
      letI : DecidableEq ↥K := fun a b => Classical.propDecidable (a = b)
      IutGlobalTorsionBasis
        (D.E.map (algebraMap D.F ↥K)).toAffine.Point D.prime.ℓ
    have hBasisType : basisType P.representationData.torsionField =
        basisType D.prime.torsionField := congrArg basisType hfield
    letI : DecidableEq ↥P.representationData.torsionField :=
      fun a b => Classical.propDecidable (a = b)
    have TP : basisType P.representationData.torsionField := P.toGlobalTorsionBasis
    change basisType D.prime.torsionField
    exact hBasisType ▸ TP
  exact IutTorsionQRootSource.ofTateFamily B T
    (iutVBadOddModSupportPort D) (iutInitialThetaTateFamilyOfTorsion D)
    (fun w => iutInitialThetaOddSupportTateFamily_badPlace D B
      (iutInitialThetaOddSupport_badPlaces_eq_fullModuliSupport D) w)
    hsix P.ell_pos P.ell_odd
    (fun w => iutInitialThetaOddSupportTateFamily_q_eq_baseParameter D w)

end

end JoshiTeich.Act1Scene1
