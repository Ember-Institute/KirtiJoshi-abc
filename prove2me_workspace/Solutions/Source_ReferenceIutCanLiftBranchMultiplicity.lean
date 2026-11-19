import Solutions.Source_ReferenceIutCanLiftPresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineCoordinateNormalizationSurjective
import ArithmeticTeichmullerSpaces.Act1Scene1.RamificationEquivSquare
import ArithmeticTeichmullerSpaces.Act1Scene1.WeierstrassBranchMultiplicity

/-!
The branch calculation of `InitialThetaBaseNormalizationBranch` for the level-one
normalization of any elliptic Weierstrass curve in characteristic zero. This identifies
the multiplicity on the sign quotient used in CanLift, Proposition 2.7, with the
two-torsion polynomial used in `OrbicurveCores/U2/HemiUnique.lean` at revision
61616dcd77fbe45c083a8ebfa7cc80728f86e841.
-/

set_option autoImplicit false

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve Polynomial JoshiTeich.Act1Scene1
open scoped Classical

universe u

noncomputable section

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

attribute [local instance] signedNormalizationAlgebra

local instance signedBaseSMul :
    SMul (coverCoordinateRing E 1 ⊥ true) (coverCoordinateRing E 1 ⊥ false) :=
  (signedNormalizationAlgebra E 1 ⊥).toSMul

local instance signedBaseModule :
    Module (coverCoordinateRing E 1 ⊥ true) (coverCoordinateRing E 1 ⊥ false) :=
  (signedNormalizationAlgebra E 1 ⊥).toModule

private theorem originalCoordinateRing_isDedekindDomain :
    IsDedekindDomain E.toAffine.CoordinateRing := by
  letI : Module.Finite k[X] E.toAffine.CoordinateRing :=
    Module.Finite.of_basis (Affine.CoordinateRing.basis E.toAffine)
  exact { IsNoetherianRing.of_finite k[X] E.toAffine.CoordinateRing,
    Ring.DimensionLEOne.of_isIntegral k[X] E.toAffine.CoordinateRing,
    coordinateRing_isIntegrallyClosed E with }

/-- The actual closed-point multiplicity of the sign quotient is two on the two-torsion
polynomial and one elsewhere. -/
theorem normalizationPresentation_signed_mult_eq_branch
    (v : Ideal (coverCoordinateRing E 1 ⊥ true)) (hv : v.IsMaximal) :
    (normalizationPresentation E 1 ⊥ true).mult v =
      if signedBasePolynomialAlgEquiv E E.twoTorsionPolynomial.toPoly ∈ v then 2 else 1 := by
  letI : v.IsMaximal := hv
  letI : Algebra.IsIntegral (coverCoordinateRing E 1 ⊥ true) (coverCoordinateRing E 1 ⊥ false) :=
    ⟨signedNormalizationRingMap_isIntegral E 1 ⊥⟩
  letI : FaithfulSMul (coverCoordinateRing E 1 ⊥ true) (coverCoordinateRing E 1 ⊥ false) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (signedNormalizationRingMap_injective E 1 ⊥)
  obtain ⟨w, hw, hwv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (R := coverCoordinateRing E 1 ⊥ true) (S := coverCoordinateRing E 1 ⊥ false) v
  letI : w.IsPrime := hw.isPrime
  letI : w.LiesOver v := hwv
  letI : IsDedekindDomain E.toAffine.CoordinateRing := originalCoordinateRing_isDedekindDomain E
  let e₁ := (signedBasePolynomialAlgEquiv E).toRingEquiv
  let e₂ := (coordinateBaseNormalizationAlgEquiv E).toRingEquiv
  have hsq (a : k[X]) : e₂ (algebraMap k[X] E.toAffine.CoordinateRing a) =
      algebraMap (coverCoordinateRing E 1 ⊥ true) (coverCoordinateRing E 1 ⊥ false) (e₁ a) :=
    coordinateToBaseNormalization_algebraMap_poly E a
  have hv₀ : v ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hv
    (notField_coverCoordinateRing E 1 ⊥ true)
  have hvmap : v.map (algebraMap (coverCoordinateRing E 1 ⊥ true)
      (coverCoordinateRing E 1 ⊥ false)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (signedNormalizationRingMap_injective E 1 ⊥)).not.mpr hv₀
  have hbranch := RamificationEquivSquare.mem_under_iff e₁ e₂ hsq v w
    E.twoTorsionPolynomial.toPoly
  calc
    _ = w.ramificationIdx (coverCoordinateRing E 1 ⊥ true) :=
      signedNormalizationMultiplicity_eq_ramificationIdx E 1 ⊥ v w
    _ = (w.comap e₂).ramificationIdx k[X] :=
      (RamificationEquivSquare.ramificationIdx_eq e₁ e₂ hsq v w hvmap).symm
    _ = _ := (WeierstrassBranchLocus.ramificationIdx_eq E.toAffine (w.comap e₂)).trans
      (congrArg (fun b : Prop => if b then (2 : ℕ) else 1) (propext hbranch))

end

end JoshiTeich.ReferenceIut.Anabelian.Genuine
