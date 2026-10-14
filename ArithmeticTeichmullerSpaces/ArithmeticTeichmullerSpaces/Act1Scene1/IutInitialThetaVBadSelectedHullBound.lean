import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadSelectedPaperAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadHullLogCost

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-SELECTED-HULL-BOUND
source: actual VBad selected root accounting and actual collated hull Haar.
fidelity: derives the selected unweighted product, negative-average and
cost bounds using exactly VBad on both sides, with its proved source
bijection. The complete odd semistable paper locus and theta identity remain
separate obligations; no larger odd-support sum is used in these bounds.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.VBadSelectedHull
open JoshiTeich.Prologue
open scoped Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (n : ℕ)
variable (σ : iutInitialThetaVBadModuliFinset D → Fin n →
  (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
variable (hσ : ∀ v i, Ideal.LiesOver (σ v i).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)
local instance selectedHullPrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime := ⟨Arithmetic.residueChar_prime v.1⟩
variable {κ : Type*}
variable (C : ∀ v : iutInitialThetaVBadModuliFinset D,
  κ → Set (VBadThetaCollatedHull.packet D n σ hσ v).Tensor)
variable (hgen : ∀ v, (VBadThetaCollatedHull.packet D n σ hσ v).scalarGenerators
  (fun i => iutInitialThetaFullQRootLogValue D (σ v i)) ⊆ ⋃ k, C v k)
variable (hunit : ∀ v k, C v k ⊆ (VBadThetaCollatedHull.packet D n σ hσ v).normalization)

include hgen hunit in
theorem selectedRootProduct_pow_lt_volume (hn : 0 < n) :
    VBadSelectedPaper.rootProduct D ^ n < VBadThetaCollatedHull.volume D n σ hσ C :=
  (pow_lt_pow_left₀ (VBadSelectedPaper.rootProduct_lt_normalizedVBadRootProduct D)
    (VBadSelectedPaper.rootProduct_pos D).le hn.ne').trans_le
    (VBadThetaCollatedHull.normalizedRootProduct_pow_le_volume D n σ hσ C hgen hunit)

include hgen hunit in
theorem negAverageAbsLog_gt_neg_selectedPaperSum (hn : 0 < n) :
    -VBadSelectedPaper.paperSum D <
      -(1 / (n : ℝ)) * |Real.log (VBadThetaCollatedHull.volume D n σ hσ C)| :=
  (neg_lt_neg (VBadSelectedPaper.referenceAbsLogQ_lt_paperSum D)).trans_le
    (VBadThetaCollatedHull.negAverageAbsLog_volume_ge_referenceLhs D n σ hσ C hgen hunit hn)

include hgen hunit in
theorem cost_lt_mul_selectedPaperSum (hn : 0 < n) :
    VBadThetaHullLogCost.cost D n σ hσ C < (n : ℝ) * VBadSelectedPaper.paperSum D :=
  ((neg_le_abs _).trans
    (VBadThetaCollatedHull.absLog_volume_le_mul_referenceAbsLogQ D n σ hσ C hgen hunit)).trans_lt
    (mul_lt_mul_of_pos_left (VBadSelectedPaper.referenceAbsLogQ_lt_paperSum D)
      (by exact_mod_cast hn))

end
end JoshiTeich.Act1Scene1.VBadSelectedHull
