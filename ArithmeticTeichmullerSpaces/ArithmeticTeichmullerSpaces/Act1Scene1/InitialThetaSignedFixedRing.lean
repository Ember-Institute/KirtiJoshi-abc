import Lean.LibrarySuggestions.Basic
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSignedNormalizationGalois
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSignedNormalizationAction

/-!
source-id: JT-SCENE1-SIGNED-NORMALIZATION-FIXED-RING-20261107
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib `IsGaloisGroup.ringEquivFixedPoints`.
fidelity: the actual signed normalization ring is identified with the
fixed subring of the actual unsigned normalization under the proved signed
quotient action. This is a coordinate-ring quotient statement, not a root
stack or arbitrary orbicurve realization.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived. Core, cusp, theta-root, and the common geometry
producer remain open; no coarse scheme pullback is asserted here.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical Pointwise
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] signedCoverNormalizationAlgebra signedCoverNormalizationGaloisAction
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance signedCoverNormalizationSMul :
    SMul (S.coverNormalizationRing true) (S.coverNormalizationRing false) :=
  S.signedCoverNormalizationAlgebra.toSMul

local instance signedCoverNormalizationModule :
    Module (S.coverNormalizationRing true) (S.coverNormalizationRing false) :=
  S.signedCoverNormalizationAlgebra.toModule

local instance signedCoverNormalizationFaithful :
    FaithfulSMul (S.coverNormalizationRing true) (S.coverNormalizationRing false) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact S.signedCoverNormalizationRingMap_injective

local instance signedCoverNormalizationGalois :
    IsGaloisGroup S.signedCoverQuotientGroup
      (S.coverNormalizationRing true) (S.coverNormalizationRing false) :=
  S.signedCoverNormalizationGaloisGroup

/-- The actual signed quotient is the fixed subring of the actual unsigned normalization. -/
noncomputable def signedNormalizationFixedRingEquiv :
    S.coverNormalizationRing true ≃+*
      FixedPoints.subsemiring (S.coverNormalizationRing false) S.signedCoverQuotientGroup :=
  IsGaloisGroup.ringEquivFixedPoints S.signedCoverQuotientGroup
    (S.coverNormalizationRing true) (S.coverNormalizationRing false)

@[simp] theorem signedNormalizationFixedRingEquiv_apply_coe
    (a : S.coverNormalizationRing true) :
    ((S.signedNormalizationFixedRingEquiv a :
      FixedPoints.subsemiring (S.coverNormalizationRing false) S.signedCoverQuotientGroup) :
      S.coverNormalizationRing false) = S.signedCoverNormalizationRingMap a := by
  rfl

@[simp] theorem signedNormalizationFixedRingEquiv_symm_apply_coe
    (x : FixedPoints.subsemiring (S.coverNormalizationRing false)
      S.signedCoverQuotientGroup) :
    S.signedCoverNormalizationRingMap
        (S.signedNormalizationFixedRingEquiv.symm x) = (x : S.coverNormalizationRing false) := by
  exact IsGaloisGroup.algebraMap_ringEquivFixedPoints_symm_apply
    S.signedCoverQuotientGroup (S.coverNormalizationRing true)
      (S.coverNormalizationRing false) x

/-- Membership in the actual fixed subring is exactly membership in the signed image. -/
theorem signedNormalization_mem_fixedRing_iff
    (x : S.coverNormalizationRing false) :
    x ∈ FixedPoints.subsemiring (S.coverNormalizationRing false) S.signedCoverQuotientGroup ↔
      ∃ a : S.coverNormalizationRing true,
        S.signedCoverNormalizationRingMap a = x := by
  change (∀ q : S.signedCoverQuotientGroup,
      S.signedCoverQuotientNormalizationAut q x = x) ↔ _
  exact S.signedCoverNormalizationInvariant_iff x

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

/- Lean 4.33.1's symbol-frequency exporter stalls on these dependent wrapper
   types. Skip their suggestion index while retaining every declaration and proof. -/
open Lean in
run_cmd do
  for name in ["signedNormalizationFixedRingEquiv_apply_coe", "signedNormalizationFixedRingEquiv_symm_apply_coe", "signedNormalization_mem_fixedRing_iff"] do
    modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env name
