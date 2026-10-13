import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRelativeQRootChoice
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaVBadRelativeQRootProduct

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-QROOT-CHOICE
source: actual local relative-root choice independence and the exact VBad product.
fidelity: permits any actual torsion-place selector over each VBad moduli place.
Its product equals the canonical product and recovers the actual reference q-pilot.
The selector is injective by unique contraction; no extra multiplicity certificate
is supplied. Paper/untilt/hull representative independence is not identified here.
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
variable (hρ : ∀ v, Ideal.LiesOver (ρ v).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal)

include hρ in
theorem iutInitialThetaVBadRootSelector_injective : Function.Injective ρ := by
  intro v w h
  apply Subtype.ext
  have hv := iutPlaceUnder_eq_of_liesOver (hρ v)
  have hw := iutPlaceUnder_eq_of_liesOver (hρ w)
  calc
    v.1 = _ := hv
    _ = iutPlaceUnder (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)) (ρ w).1 := by rw [h]
    _ = w.1 := hw.symm

def iutInitialThetaVBadRelativeQRootProductOf : ℝ :=
  ∏ v : iutInitialThetaVBadModuliFinset D, iutInitialThetaRelativeQRootFactorAt D v.1 (ρ v)

def iutInitialThetaNormalizedVBadRelativeQRootProductOf : ℝ :=
  iutInitialThetaVBadRelativeQRootProductOf D ρ ^
    (1 / (Module.finrank ℚ ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))

include hρ in
theorem iutInitialThetaVBadRelativeQRootProductOf_eq_canonical :
    iutInitialThetaVBadRelativeQRootProductOf D ρ = iutInitialThetaVBadRelativeQRootProduct D := by
  unfold iutInitialThetaVBadRelativeQRootProductOf iutInitialThetaVBadRelativeQRootProduct
  exact Finset.prod_congr rfl fun v _ =>
    iutInitialThetaRelativeQRootFactorAt_eq_selectedFactor D (iutInitialThetaVBadModuliAt D v) (ρ v) (hρ v)

include hρ in
theorem iutInitialThetaNormalizedVBadRelativeQRootProductOf_eq_canonical :
    iutInitialThetaNormalizedVBadRelativeQRootProductOf D ρ =
      iutInitialThetaNormalizedVBadRelativeQRootProduct D := by
  unfold iutInitialThetaNormalizedVBadRelativeQRootProductOf iutInitialThetaNormalizedVBadRelativeQRootProduct
  rw [iutInitialThetaVBadRelativeQRootProductOf_eq_canonical D ρ hρ]

include hρ in
theorem iutInitialThetaNormalizedVBadRelativeQRootProductOf_negLog_eq_referenceAbsLogQ :
    -Real.log (iutInitialThetaNormalizedVBadRelativeQRootProductOf D ρ) =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  rw [iutInitialThetaNormalizedVBadRelativeQRootProductOf_eq_canonical D ρ hρ]
  exact iutInitialThetaNormalizedVBadRelativeQRootProduct_negLog_eq_referenceAbsLogQ D

include hρ in
theorem iutInitialThetaVBadRelativeQRootProductOf_choice_independent
    (τ : iutInitialThetaVBadModuliFinset D → (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (hτ : ∀ v, Ideal.LiesOver (τ v).1.maximalIdeal.asIdeal v.1.maximalIdeal.asIdeal) :
    iutInitialThetaVBadRelativeQRootProductOf D ρ = iutInitialThetaVBadRelativeQRootProductOf D τ := by
  rw [iutInitialThetaVBadRelativeQRootProductOf_eq_canonical D ρ hρ,
    iutInitialThetaVBadRelativeQRootProductOf_eq_canonical D τ hτ]

end
end JoshiTeich.Act1Scene1
