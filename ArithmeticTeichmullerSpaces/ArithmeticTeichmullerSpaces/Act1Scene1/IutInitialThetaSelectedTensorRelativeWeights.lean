import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedTensorDegreeVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionRelativeDegree

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-RELATIVE-WEIGHTS
source: Joshi III eq:weights (3554--3557), actual torsion/moduli contraction
and relative completion algebra, and the actual degree-normalized tensor Haar.
fidelity: constructs the candidate relative-degree weights on the actual selected
prime fibre. The numerical product is indexed by this presentation. Its equality
with a single power of degreeVolume requires common moduli local degrees; paper
carrier, norm, maximal order and hull identifications remain proof obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.SelectedThetaTensor
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) [Fact p.Prime]
local instance relativeIntegralModule : Module ℤ_[p] (packet D p).Tensor :=
  Module.compHom (packet D p).Tensor (algebraMap ℤ_[p] ℚ_[p])

abbrev moduliAt (i : Fin (Fintype.card ↥(fiber D p))) :
    NumberField.FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) :=
  iutPlaceUnder (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) (sourceAt D p i).1

def relativeDegree (i : Fin (Fintype.card ↥(fiber D p))) : ℕ :=
  letI := LocalCompletion.relativeAlgebra (iutPlaceUnder_liesOver
    (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) (sourceAt D p i).1)
  Module.finrank
    (LocalCompletion.completionAt ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) (moduliAt D p i))
    (LocalCompletion.completionAt ↥D.prime.torsionField (sourceAt D p i).1)

def relativeWeight (i : Fin (Fintype.card ↥(fiber D p))) : ℝ := 1 / (relativeDegree D p i : ℝ)

theorem relativeDegree_eq_ramification_inertia (i : Fin (Fintype.card ↥(fiber D p))) :
    relativeDegree D p i = Arithmetic.relRamIdx (sourceAt D p i).1 (moduliAt D p i) *
      Arithmetic.relInertDeg (sourceAt D p i).1 (moduliAt D p i) :=
  LocalCompletion.finrank_relativeAlgebra_eq_ramification_inertia
    (iutPlaceUnder_liesOver (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) (sourceAt D p i).1)

theorem relativeWeight_eq_localDeg_ratio (i : Fin (Fintype.card ↥(fiber D p))) :
    relativeWeight D p i =
      (Arithmetic.localDeg (moduliAt D p i) : ℝ) / Arithmetic.localDeg (sourceAt D p i).1 :=
  LocalCompletion.inverse_relativeFinrank_eq_localDeg_ratio
    (iutPlaceUnder_liesOver (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) (sourceAt D p i).1)

theorem relativeWeight_mem_Ioc (i : Fin (Fintype.card ↥(fiber D p))) :
    relativeWeight D p i ∈ Set.Ioc (0 : ℝ) 1 :=
  LocalCompletion.inverse_relativeFinrank_mem_Ioc
    (iutPlaceUnder_liesOver (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) (sourceAt D p i).1)

/-- The relative-degree weighted root product on the actual selected presentation. -/
def relativeRootVolume : ℝ :=
  ∏ i, ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot (sourceAt D p i)‖ ^ relativeWeight D p i

theorem relativeRootVolume_eq_localDeg_product :
    relativeRootVolume D p =
      ∏ i, ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot (sourceAt D p i)‖ ^
        ((Arithmetic.localDeg (moduliAt D p i) : ℝ) / Arithmetic.localDeg (sourceAt D p i).1) := by
  unfold relativeRootVolume
  simp only [relativeWeight_eq_localDeg_ratio]

theorem relativeRootVolume_negLog_eq_ordp_sum :
    -Real.log (relativeRootVolume D p) =
      ∑ i, (Arithmetic.localDeg (moduliAt D p i) : ℝ) *
        Arithmetic.ordp (sourceAt D p i).1
          ((iutInitialThetaOddSupportTorsionQRootSource D).qroot (sourceAt D p i)) * Real.log p := by
  rw [relativeRootVolume_eq_localDeg_product,
    Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (norm_pos_iff.mpr
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)) _).ne'),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.log_rpow (norm_pos_iff.mpr
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _))]
  unfold Arithmetic.ordp
  rw [(sourceAt_selected_residueChar D p i).2]
  have hd : (Arithmetic.localDeg (sourceAt D p i).1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.localDeg_pos _).ne'
  have hp : Real.log p ≠ 0 := (Real.log_pos
    (by exact_mod_cast (Fact.out : p.Prime).one_lt)).ne'
  field_simp [hd, hp]
  <;> ring

theorem relativeRootVolume_eq_degreeVolume_pow_of_common_moduliDegree (d : ℕ)
    (hd : ∀ i : Fin (Fintype.card ↥(fiber D p)), Arithmetic.localDeg (moduliAt D p i) = d) :
    relativeRootVolume D p = (packet D p).degreeVolume (region D p) ^ d := by
  rw [relativeRootVolume_eq_localDeg_product, region_degreeVolume_eq_rootNorm_product,
    ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hd i, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  ring

end
end JoshiTeich.Act1Scene1.SelectedThetaTensor
