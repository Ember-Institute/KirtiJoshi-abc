import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedTensorDetHaar
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorRawVolume

/-!
source-id: JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-RAW-VOLUME
source: actual selected log/root norm identity and the proved raw tensor Haar law.
fidelity: computes selected region Haar from actual root norms. No paper weight,
theta hull, Bloch-Kato identity, or volume transfer certificate is supplied.
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
local instance rawFactorAlgebra (i : Fin (Fintype.card ↥(fiber D p))) : Algebra ℚ_[p] ((packet D p).Factor i) :=
  LocalCompletion.padicAlgebra ((packet D p).residueChar_eq i)
local instance rawFactorFinite (i : Fin (Fintype.card ↥(fiber D p))) : Module.Finite ℚ_[p] ((packet D p).Factor i) :=
  LocalCompletion.finite_padicAlgebra ((packet D p).residueChar_eq i)
local instance rawIntegralModule : Module ℤ_[p] (packet D p).Tensor :=
  Module.compHom (packet D p).Tensor (algebraMap ℤ_[p] ℚ_[p])

theorem logFactorNorm_norm_eq_rootNorm (i : Fin (Fintype.card ↥(fiber D p))) :
    ‖logFactorNorm D p i‖ =
      ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot (sourceAt D p i)‖ := by
  have hn := iutInitialThetaFullQRootLogValue_norm_eq D (sourceAt D p i)
  have hne : iutInitialThetaFullQRootLogValue D (sourceAt D p i) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hn]
    exact norm_ne_zero_iff.mpr ((iutInitialThetaOddSupportTorsionQRootSource D).qroot_ne_zero _)
  exact (LocalCompletion.norm_algebraNorm_eq_completionNorm_of_contracting
    (sourceAt D p i).1 ((packet D p).residueChar_eq i) _ hne
    (hn.trans_lt (iutInitialThetaFullQRoot_norm_lt_one D _))).trans hn

theorem region_normalizedHaar_eq_rootNorm_product :
    (packet D p).normalizedHaar (region D p) =
      ENNReal.ofReal (∏ i, ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot (sourceAt D p i)‖ ^
        FiniteTensorMatrix.otherDimension
          (fun j => Module.finrank ℚ_[p] ((packet D p).Factor j)) i) := by
  rw [region_normalizedHaar_eq_factorNorm_product]
  simp only [logFactorNorm_norm_eq_rootNorm]

end
end JoshiTeich.Act1Scene1.SelectedThetaTensor
