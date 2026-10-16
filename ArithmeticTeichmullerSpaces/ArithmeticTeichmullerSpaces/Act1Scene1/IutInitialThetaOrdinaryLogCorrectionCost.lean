import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOrdinaryLogCollation

/-!
source-id: JT-SCENE1-ACTUAL-ORDINARY-LOG-CORRECTION-COST
source: completion norm of the residue prime, actual odd support and the
normalization Haar correction; Joshi III 3226--3236, 3520--3574.
fidelity: evaluates the single-factor correction cost as the sum of
localDeg(moduli)/inertDeg(source) times log(residueChar(source)).
boundary: Scene1/Derived; no BK, different-untilt or paper volume identity.
-/

namespace JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance correctionCostPrime (v : iutInitialThetaOddModSupportFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩
local instance correctionCostCharZero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (PrincipalUnitKummer.localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem negLog_norm_paperScale_eq_localDeg
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    -Real.log ‖(LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : PrincipalUnitKummer.localField D s)‖ =
      (Arithmetic.localDeg s.1 : ℝ) * Real.log (Arithmetic.residueChar s.1) := by
  have hp2 : Arithmetic.residueChar s.1 ≠ 2 := by
    intro h
    have ho := PrincipalUnitKummer.smallLift_residueChar_odd D s
    rw [h] at ho
    norm_num at ho
  have hn := LocalCompletion.norm_residueChar_eq_inv_pow_localDeg s.1
  rw [map_natCast] at hn
  rw [LocalPadicLog.paperScale, if_neg hp2, hn, Real.log_pow, Real.log_inv]
  ring

def localCorrectionCost (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  (Arithmetic.localDeg v.1 : ℝ) / Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1 *
    Real.log (Arithmetic.residueChar (FullSupportPaperWeightedHull.selected D v).1)

theorem localCorrectionCost_pos (v : iutInitialThetaOddModSupportFinset D) :
    0 < localCorrectionCost D v := by
  apply mul_pos (div_pos (by exact_mod_cast Arithmetic.localDeg_pos v.1)
    (by exact_mod_cast Arithmetic.inertDeg_pos _))
  exact Real.log_pos (by exact_mod_cast (Arithmetic.residueChar_prime _).one_lt)

theorem negLog_degreeCorrection_one
    (v : iutInitialThetaOddModSupportFinset D) :
    -Real.log (degreeCorrection D 1 v) =
      Real.log (Arithmetic.residueChar (FullSupportPaperWeightedHull.selected D v).1) := by
  let s := FullSupportPaperWeightedHull.selected D v
  have hs : (Arithmetic.localDeg s.1 : ℝ) ≠ 0 := by exact_mod_cast (Arithmetic.localDeg_pos s.1).ne'
  have hn : 0 < ‖(LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : PrincipalUnitKummer.localField D s)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (LocalPadicLog.paperScale_ne_zero (Arithmetic.residueChar_prime s.1)))
  change -Real.log (∏ _ : Fin 1,
    ‖(LocalPadicLog.paperScale (Arithmetic.residueChar s.1) : PrincipalUnitKummer.localField D s)‖ ^
      (1 / (Arithmetic.localDeg s.1 : ℝ))) = _
  rw [Fin.prod_const, pow_one, Real.log_rpow hn, neg_mul_eq_mul_neg,
    negLog_norm_paperScale_eq_localDeg D s]
  field_simp [hs]
  rfl

theorem negLog_localCorrection_one (v : iutInitialThetaOddModSupportFinset D) :
    -Real.log (localCorrection D 1 v) = localCorrectionCost D v := by
  rw [localCorrection, Real.log_rpow (pow_pos (degreeCorrection_pos D 1 v) _), Real.log_pow]
  calc
    _ = (1 / (Arithmetic.inertDeg (FullSupportPaperWeightedHull.selected D v).1 : ℝ)) *
        (Arithmetic.localDeg v.1 : ℝ) * (-Real.log (degreeCorrection D 1 v)) := by ring
    _ = _ := by rw [negLog_degreeCorrection_one]; unfold localCorrectionCost; ring

theorem correctionCost_eq_sum :
    -Real.log (correction D 1) = ∑ v : iutInitialThetaOddModSupportFinset D, localCorrectionCost D v := by
  have hc (v : iutInitialThetaOddModSupportFinset D) : localCorrection D 1 v ≠ 0 :=
    (Real.rpow_pos_of_pos (pow_pos (degreeCorrection_pos D 1 v) _) _).ne'
  rw [correction, Real.log_prod (fun v _ => hc v), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun v _ => negLog_localCorrection_one D v)

def selectedPaperTerm (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  -Real.log (actualPaperRootNorm D (FullSupportPaperWeightedHull.selected D v))

def correctedLocalCost (v : iutInitialThetaOddModSupportFinset D) : ℝ :=
  FullSupportPaperWeightedHull.weight D v * selectedPaperTerm D v + localCorrectionCost D v

theorem correctedCost_eq_sum :
    FullSupportPaperWeightedHull.weightedPaperSum D - Real.log (correction D 1) =
      ∑ v : iutInitialThetaOddModSupportFinset D, correctedLocalCost D v := by
  rw [sub_eq_add_neg, correctionCost_eq_sum, FullSupportPaperWeightedHull.weightedPaperSum,
    ← Finset.sum_add_distrib]
  rfl

theorem selectedPaperSum_eq_sum_terms :
    iutInitialThetaSelectedQRootPaperSum D = ∑ v : iutInitialThetaOddModSupportFinset D, selectedPaperTerm D v := by
  rw [← actualSelectedPaperRootNormProduct_negLog_eq_paperSum D,
    FullSupportPaperWeightedHull.selectedPaperRootProduct_eq_moduliProduct,
    Real.log_prod (fun v _ => (actualPaperRootNorm_mem_Ioo D _).1.ne'), ← Finset.sum_neg_distrib]
  rfl

end
end JoshiTeich.Act1Scene1.OrdinaryKummerLogHull
