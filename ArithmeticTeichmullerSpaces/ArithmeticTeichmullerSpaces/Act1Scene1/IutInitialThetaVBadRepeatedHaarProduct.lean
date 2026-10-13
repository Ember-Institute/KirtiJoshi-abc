import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepeatedRootHaar
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadQRootChoice

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-REPEATED-HAAR-PRODUCT
source: actual repeated local log-scalar tensor Haar volumes and exact VBad
relative-root product accounting. Each packet has a fixed moduli place.
fidelity: derives the globally normalized product from actual local Haar;
its negative log is n times the actual reference q-pilot and its value is
independent of the legal over-place selector. The local-degree and global-degree
corrections are explicit numerical powers, not an identification with paper
thetaVolume or a hull measure.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (ρ : iutInitialThetaVBadModuliFinset D →
  (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
variable (n : ℕ)

def iutInitialThetaVBadRepeatedHaarProduct : ℝ :=
  (∏ v : iutInitialThetaVBadModuliFinset D, RepeatedThetaRoot.moduliVolume D (ρ v) n v.1) ^
    (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))

variable (hρ : ∀ v, Ideal.LiesOver (ρ v).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)

include hρ in
theorem iutInitialThetaVBadRepeatedHaarProduct_eq_normalizedRootProduct_pow :
    iutInitialThetaVBadRepeatedHaarProduct D ρ n =
      iutInitialThetaNormalizedVBadRelativeQRootProduct D ^ n := by
  have hprod : (∏ v : iutInitialThetaVBadModuliFinset D,
      RepeatedThetaRoot.moduliVolume D (ρ v) n v.1) =
      iutInitialThetaVBadRelativeQRootProductOf D ρ ^ n := by
    unfold iutInitialThetaVBadRelativeQRootProductOf
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun v _ => RepeatedThetaRoot.moduliVolume_eq_relativeFactor_pow D (ρ v) n v.1
  have hpos : 0 ≤ iutInitialThetaVBadRelativeQRootProductOf D ρ := by
    rw [iutInitialThetaVBadRelativeQRootProductOf_eq_canonical D ρ hρ]
    exact (iutInitialThetaVBadRelativeQRootProduct_pos D).le
  rw [iutInitialThetaVBadRepeatedHaarProduct, hprod, ← Real.rpow_pow_comm hpos]
  change iutInitialThetaNormalizedVBadRelativeQRootProductOf D ρ ^ n = _
  rw [iutInitialThetaNormalizedVBadRelativeQRootProductOf_eq_canonical D ρ hρ]

include hρ in
theorem iutInitialThetaVBadRepeatedHaarProduct_negLog_eq_mul_referenceAbsLogQ :
    -Real.log (iutInitialThetaVBadRepeatedHaarProduct D ρ n) =
      (n : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  rw [iutInitialThetaVBadRepeatedHaarProduct_eq_normalizedRootProduct_pow D ρ n hρ, Real.log_pow,
    ← iutInitialThetaNormalizedVBadRelativeQRootProduct_negLog_eq_referenceAbsLogQ D]
  ring

include hρ in
theorem iutInitialThetaVBadRepeatedHaarProduct_choice_independent
    (τ : iutInitialThetaVBadModuliFinset D → (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hτ : ∀ v, Ideal.LiesOver (τ v).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal) :
    iutInitialThetaVBadRepeatedHaarProduct D ρ n = iutInitialThetaVBadRepeatedHaarProduct D τ n := by
  rw [iutInitialThetaVBadRepeatedHaarProduct_eq_normalizedRootProduct_pow D ρ n hρ,
    iutInitialThetaVBadRepeatedHaarProduct_eq_normalizedRootProduct_pow D τ n hτ]

end
end JoshiTeich.Act1Scene1
