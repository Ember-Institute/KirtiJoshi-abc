import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTateFamily
import ArithmeticTeichmullerSpaces.Act1Scene1.IutTateParameterCompletion
import ArithmeticTeichmullerSpaces.Act1Scene1.IutPlacesOver
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PlaceUnder

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open IsDedekindDomain.HeightOneSpectrum
open NumberField TateCurvesTheta
open scoped NumberField Valued

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-ODD-SUPPORT-Q-PARAMETER
source: `iut`: `refer/iut/Iut/Tripod/CyclicTorsion.lean`,
`EllipticCurveData.VBadOdd`; `refer/iut/Iut/Cor312/ThetaData/PlaceUnder.lean`,
`one_lt_valuation_j_of_mult`; `refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`,
`tateFamilyOfTorsion`; `TateCurvesTheta`, `TateParameter.exists_tateParameter_tateJ_eq`
and `TateParameter.tateJ_injective`.
fidelity: constructs a base-completion Tate parameter at every place in the full odd
multiplicative moduli support, including residue characteristic `ell`, and identifies
its image with the q-parameter of the Tate structure at the actual selected torsion-field
place. This is a local source theorem; it does not identify the resulting local factors
with the global IUT weighted sum or construct theta-volume accounting.
boundary: Scene1/Derived
-/

private noncomputable def iutInitialThetaModuliJ
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) :=
  ⟨D.E.j, IntermediateField.mem_adjoin_simple_self ℚ D.E.j⟩

private theorem iut_norm_embedding_le_one_iff
    {F : Type u} [Field F] [NumberField F] (w : NumberField.FinitePlace F) (x : F) :
    ‖(NumberField.FinitePlace.embedding w.maximalIdeal x :
      JoshiTeich.ReferenceIut.localCompletion w)‖ ≤ 1 ↔
      w.maximalIdeal.valuation F x ≤ 1 := by
  rw [JoshiTeich.ReferenceIut.norm_le_one_iff_valued, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation']

private theorem iutCurve_j_eq_div_of_field
    {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic] :
    E.j = E.c₄ ^ 3 / E.Δ := by
  rw [WeierstrassCurve.j, div_eq_inv_mul]
  congr 1
  rw [← WeierstrassCurve.coe_Δ', ← Units.val_inv_eq_inv_val]

theorem iutInitialThetaOddSupport_j_norm_gt_one
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutVBadOddModSupportPort D) :
    1 < ‖(NumberField.FinitePlace.embedding v.maximalIdeal
      (iutInitialThetaModuliJ D) : JoshiTeich.ReferenceIut.localCompletion v)‖ := by
  obtain ⟨w, hwv⟩ := hv.2.1
  have hmult := hv.2.2 w hwv
  have hval := JoshiTeich.ReferenceIut.one_lt_valuation_j_of_mult D.E w hmult
  have hval_le_iff :
      w.maximalIdeal.valuation D.F D.E.j ≤ 1 ↔
        v.maximalIdeal.valuation _ (iutInitialThetaModuliJ D) ≤ 1 := by
    haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
    change w.maximalIdeal.valuation D.F
        (algebraMap _ _ (iutInitialThetaModuliJ D)) ≤ 1 ↔ _
    rw [← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver
      D.F v.maximalIdeal w.maximalIdeal (iutInitialThetaModuliJ D)]
    exact pow_le_one_iff_of_nonneg zero_le
      (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.maximalIdeal.asIdeal
        v.maximalIdeal.ne_bot).ne'
  have hmod_not_le :
      ¬ v.maximalIdeal.valuation _ (iutInitialThetaModuliJ D) ≤ 1 := by
    intro hmod
    exact (not_le_of_gt hval) (hval_le_iff.mpr hmod)
  apply lt_of_not_ge
  intro hnorm
  have hvalued := (iut_norm_embedding_le_one_iff v (iutInitialThetaModuliJ D)).mp hnorm
  exact hmod_not_le hvalued

/-- The full odd multiplicative support on the moduli field is finite. Its
places all lie in the finite multiplicative support of the actual curve's
moduli `j`-invariant. -/
theorem iutInitialThetaOddModSupport_finite
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (iutVBadOddModSupportPort D).Finite := by
  by_cases hj : iutInitialThetaModuliJ D = 0
  · refine Set.Finite.subset Set.finite_empty ?_
    intro v hv
    have hnorm := iutInitialThetaOddSupport_j_norm_gt_one D v hv
    rw [hj, map_zero] at hnorm
    exact absurd hnorm (not_lt_of_ge (by norm_num))
  · refine (NumberField.FinitePlace.hasFiniteMulSupport hj).subset ?_
    intro v hv
    rw [Function.mem_mulSupport, ← NumberField.FinitePlace.norm_embedding_eq]
    intro hnorm
    have hle :
        ‖(NumberField.FinitePlace.embedding v.maximalIdeal
          (iutInitialThetaModuliJ D) : JoshiTeich.ReferenceIut.localCompletion v)‖ ≤ 1 := by
      rw [hnorm]
    exact absurd hle
      (not_le_of_gt (iutInitialThetaOddSupport_j_norm_gt_one D v hv))

/-- The full-support places above the moduli support form a finite carrier in
the actual torsion field. -/
theorem iutInitialThetaOddSupportOverTorsion_finite
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    (iutBadPlacesOver
      (k := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
      (K := ↥D.prime.torsionField) (iutVBadOddModSupportPort D)).Finite :=
  iutBadPlacesOver_finite (iutVBadOddModSupportPort D)
    (iutInitialThetaOddModSupport_finite D)

noncomputable def iutInitialThetaOddSupportBaseTateParameter
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutVBadOddModSupportPort D) :
    TateParameter (JoshiTeich.ReferenceIut.localCompletion v) :=
  Classical.choose (TateParameter.exists_tateParameter_tateJ_eq
    (JoshiTeich.ReferenceIut.twelve_ne_zero v)
    (iutInitialThetaOddSupport_j_norm_gt_one D v hv))

theorem iutInitialThetaOddSupportBaseTateParameter_tateJ_eq
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutVBadOddModSupportPort D) :
    (iutInitialThetaOddSupportBaseTateParameter D v hv).tateJ =
      NumberField.FinitePlace.embedding v.maximalIdeal (iutInitialThetaModuliJ D) :=
  Classical.choose_spec (TateParameter.exists_tateParameter_tateJ_eq
    (JoshiTeich.ReferenceIut.twelve_ne_zero v)
    (iutInitialThetaOddSupport_j_norm_gt_one D v hv))

private theorem iutInitialThetaAlgebraModK_eq
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

private theorem iutInitialThetaModuliJ_map_eq
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    algebraMap (↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
      ↥D.prime.torsionField (iutInitialThetaModuliJ D) =
      algebraMap D.F ↥D.prime.torsionField D.E.j := by
  calc
    _ = algebraMap D.F ↥D.prime.torsionField
        (algebraMap (↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) D.F
          (iutInitialThetaModuliJ D)) :=
      @IsScalarTower.algebraMap_apply
        (↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) D.F
        ↥D.prime.torsionField _ _ _ _ _ D.algebraModK D.towerModK
        (iutInitialThetaModuliJ D)
    _ = _ := rfl

theorem iutInitialThetaFinitePlaceSection_liesOver_moduli
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) :
    JoshiTeich.ReferenceIut.FinitePlace.LiesOver
      (iutInitialThetaFinitePlaceSection D v) v := by
  exact (iutInitialThetaAlgebraModK_eq D) ▸
    iutInitialThetaFinitePlaceSection_liesOver D v

private theorem iutInitialThetaFinitePlaceLiesOver_toCanonical
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)}
    {w : NumberField.FinitePlace ↥D.prime.torsionField}
    (hvw : JoshiTeich.ReferenceIut.FinitePlace.LiesOver w v) :
    @JoshiTeich.ReferenceIut.FinitePlace.LiesOver
      _ _ _ _ _ _
      (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E).instAlgebraSubtypeMem w v :=
  (iutInitialThetaAlgebraModK_eq D) ▸ hvw

/-- At every selected representative of the full odd multiplicative support, the
actual torsion-field Tate family parameter is the image of the locally constructed
base parameter. This includes residue characteristic `ell`. -/
theorem iutInitialThetaOddSupportSelected_q_eq_baseParameter
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutVBadOddModSupportPort D) :
    ((iutInitialThetaFinitePlaceSection_tateStructure D v hv).t.q :
      (iutInitialThetaFinitePlaceSection D v).maximalIdeal.adicCompletion
        ↥D.prime.torsionField) =
      iutEmbedCompletion (iutInitialThetaFinitePlaceSection_liesOver_moduli D v)
        ((iutInitialThetaOddSupportBaseTateParameter D v hv).q) := by
  let v' := iutInitialThetaFinitePlaceSection D v
  let t := iutInitialThetaOddSupportBaseTateParameter D v hv
  let S := iutInitialThetaFinitePlaceSection_tateStructure D v hv
  have hvw : Ideal.LiesOver v'.maximalIdeal.asIdeal v.maximalIdeal.asIdeal :=
    iutInitialThetaFinitePlaceSection_liesOver_moduli D v
  have hmodJ := iutInitialThetaOddSupportBaseTateParameter_tateJ_eq D v hv
  have hJ : (iutEmbedTateParameter hvw t).tateJ = S.t.tateJ := by
    calc
      (iutEmbedTateParameter hvw t).tateJ = iutEmbedCompletion hvw t.tateJ :=
        (iutTateJ_embed hvw t).symm
      _ = NumberField.FinitePlace.embedding v'.maximalIdeal
          (algebraMap D.F ↥D.prime.torsionField D.E.j) := by
        rw [hmodJ, iutEmbedCompletion_embedding hvw, iutInitialThetaModuliJ_map_eq D]
      _ = (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField v').j := by
        rw [iutCurve_j_eq_div_of_field (E := D.E),
          iutCurve_j_eq_div_of_field
            (E := JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField v')]
        simp only [JoshiTeich.ReferenceIut.curveKw, JoshiTeich.ReferenceIut.curveK,
          WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ, map_div₀, map_pow]
      _ = S.t.tateJ := by
        calc
          (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField v').j =
              (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField v').c₄ ^ 3 /
                (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField v').Δ :=
            iutCurve_j_eq_div_of_field _
          _ = S.t.tateJ := (iutTateStructure_tateJ_eq S).symm
  simpa [v', t, S] using
    iutTateParameter_q_eq_of_tateJ_eq hvw t S.t hJ

/-- At every torsion-field place above the full odd multiplicative support, the
Tate-family parameter is the image of the base-completion parameter. This
removes dependence on the particular finite-place section representative. -/
theorem iutInitialThetaOddSupport_q_eq_baseParameter_of_liesOver
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (v : NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ iutVBadOddModSupportPort D)
    (w : NumberField.FinitePlace ↥D.prime.torsionField)
    (hvw : JoshiTeich.ReferenceIut.FinitePlace.LiesOver w v) :
    (((iutInitialThetaTateFamilyOfTorsion D).S w ⟨v, hv,
      iutInitialThetaFinitePlaceLiesOver_toCanonical D hvw⟩).t.q :
      w.maximalIdeal.adicCompletion ↥D.prime.torsionField) =
      iutEmbedCompletion hvw
        ((iutInitialThetaOddSupportBaseTateParameter D v hv).q) := by
  let t := iutInitialThetaOddSupportBaseTateParameter D v hv
  let hBad := iutInitialThetaFinitePlaceLiesOver_toCanonical D hvw
  let S := (iutInitialThetaTateFamilyOfTorsion D).S w ⟨v, hv, hBad⟩
  have hJ : (iutEmbedTateParameter hvw t).tateJ = S.t.tateJ := by
    calc
      (iutEmbedTateParameter hvw t).tateJ = iutEmbedCompletion hvw t.tateJ :=
        (iutTateJ_embed hvw t).symm
      _ = NumberField.FinitePlace.embedding w.maximalIdeal
          (algebraMap D.F ↥D.prime.torsionField D.E.j) := by
        rw [iutInitialThetaOddSupportBaseTateParameter_tateJ_eq D v hv,
          iutEmbedCompletion_embedding hvw, iutInitialThetaModuliJ_map_eq D]
      _ = (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField w).j := by
        rw [iutCurve_j_eq_div_of_field (E := D.E),
          iutCurve_j_eq_div_of_field
            (E := JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField w)]
        simp only [JoshiTeich.ReferenceIut.curveKw, JoshiTeich.ReferenceIut.curveK,
          WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ, map_div₀, map_pow]
      _ = (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField w).c₄ ^ 3 /
          (JoshiTeich.ReferenceIut.curveKw D.E D.prime.torsionField w).Δ :=
        iutCurve_j_eq_div_of_field _
      _ = S.t.tateJ := (iutTateStructure_tateJ_eq S).symm
  simpa [t, S] using iutTateParameter_q_eq_of_tateJ_eq hvw t S.t hJ

end

end JoshiTeich.Act1Scene1
