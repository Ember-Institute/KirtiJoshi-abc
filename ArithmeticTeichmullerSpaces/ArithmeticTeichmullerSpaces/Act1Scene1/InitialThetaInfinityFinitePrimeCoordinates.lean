/-
Adapted from the already vendored GenuineNormalizationPrimeInertia.lean.
original-path: refer/iut/Iut/Anabelian/Genuine/Homs.lean
original-author: Christian Merten <lana@merten.dev> (Git author)
original-file-authors: The iut contributors
original-commit: b51b94cad5c729f753ed0790b5fb95d9d65aaff1
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modifications: descend the same coordinates into the same actual finite normal
closure on the inverse chart. Use actual lower-field membership to fix the
base point, and the new pole-division theorem with the seed's own shift.
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityDivisionClosure
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityPoleInertia
import ArithmeticTeichmullerSpaces.Act1Scene1.FiniteInversePrimePoleInertia

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`.
fidelity: actual finite prime inertia, over the same actual lower elliptic
field, fixes the original ell-division coordinates in its actual finite normal
closure. No ambient inertia lift or independent point input is assumed.
boundary: this is the finite-inertia containment input. Ramification index one,
translation inertia bottom, prime-stabilizer freeness and cusp identities are
not asserted here.
-/
namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
open WeierstrassCurve IsDedekindDomain
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open FunctionFieldNormalization
open scoped Classical IntermediateField.algebraAdjoinAdjoin Pointwise
universe u
noncomputable section
attribute [local instance 2000] Classical.propDecidable
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] inverseCoordinateRationalBase_coefficientAlgebra
  inverseCoordinateRationalBase_coefficientSMul inverseCoordinateRationalBase_coefficientModule
  inverseCoordinatePolynomialBaseRationalBaseAlgebra inverseCoordinatePolynomialBaseRationalBaseSMul
  inverseCoordinatePolynomialBaseRationalBaseModule inverseCoordinatePolynomialBaseRationalBaseTower
  infinityDivisionNormalClosure_field infinityDivisionNormalClosure_rationalAlgebra
  infinityDivisionNormalClosure_baseAlgebra infinityDivisionNormalClosure_baseSMul
  infinityDivisionNormalClosure_baseModule infinityDivisionNormalClosure_coefficientAlgebra
  infinityDivisionNormalClosure_coefficientSMul infinityDivisionNormalClosure_coefficientModule
  infinityDivisionNormalClosure_coefficientBaseTower infinityDivisionNormalClosure_baseTower
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

local instance infinityDivisionClosure_separable :
    Algebra.IsSeparable
      (rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      S.infinityDivisionNormalClosure :=
  @IsGalois.to_isSeparable _ _ _ _ _ S.isGalois_infinityDivisionNormalClosure

local instance infinityDivisionClosureRing_baseAlgebra :
    Algebra (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure) :=
  (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure).algebra

local instance infinityDivisionClosureRing_dedekind :
    IsDedekindDomain (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure) :=
  dedekindRing _ S.infinityTranslation_inverseCoordinate_transcendental _
local instance infinityDivisionClosureRing_fraction :
    IsFractionRing (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure)
      S.infinityDivisionNormalClosure := fractionFieldRing _ _
attribute [local instance] galoisNormalizationCoeffComm fieldRingAction

set_option maxHeartbeats 1000000 in
theorem infinityClosurePrime_inertia_fixes_coordinates
    (p : HeightOneSpectrum (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure))
    (hp : algebraMap
      (polynomialBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹)
      (coordRing (Genuine.xG S.prime.EK)⁻¹ S.infinityDivisionNormalClosure)
      (polynomialCoordinate (Genuine.xG S.prime.EK)⁻¹) ∈ p.asIdeal)
    (τ : S.infinityDivisionNormalClosure ≃ₐ[
      rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹]
      S.infinityDivisionNormalClosure)
    (hτ : τ ∈ p.asIdeal.inertia
      (S.infinityDivisionNormalClosure ≃ₐ[
        rationalBase ↥S.prime.torsionField (Genuine.xG S.prime.EK)⁻¹]
        S.infinityDivisionNormalClosure))
    (hF : τ ∈ fixSub S.infinityDivisionNormalClosure S.infinityTranslationBaseField) :
    τ ⟨ptX (Genuine.Qpt S.prime.EK S.prime.ℓ),
        S.infinityDivisionNormalClosure_Qpt_coordinates_mem.1⟩ =
      ⟨ptX (Genuine.Qpt S.prime.EK S.prime.ℓ),
        S.infinityDivisionNormalClosure_Qpt_coordinates_mem.1⟩ ∧
      τ ⟨ptY (Genuine.Qpt S.prime.EK S.prime.ℓ),
        S.infinityDivisionNormalClosure_Qpt_coordinates_mem.2⟩ =
      ⟨ptY (Genuine.Qpt S.prime.EK S.prime.ℓ),
        S.infinityDivisionNormalClosure_Qpt_coordinates_mem.2⟩ := by
  let E := S.prime.EK
  let N := S.infinityDivisionNormalClosure
  obtain ⟨x, y, h, hQ⟩ : ∃ (x y : Genuine.Ω E)
      (h : (E⁄(Genuine.Ω E)).toAffine.Nonsingular x y),
      Genuine.Qpt E S.prime.ℓ = Affine.Point.some x y h := by
    rcases hq : Genuine.Qpt E S.prime.ℓ with _ | ⟨x, y, h⟩
    · exact False.elim (Genuine.divSys_ne_zero E (Genuine.effLevel S.prime.ℓ)
        (Genuine.effLevel_pos S.prime.ℓ) hq)
    · exact ⟨x, y, h, rfl⟩
  have hxN : x ∈ N := by
    have hx := S.infinityDivisionNormalClosure_Qpt_coordinates_mem.1
    change ptX (Genuine.Qpt E S.prime.ℓ) ∈ N at hx
    simpa only [hQ, ptX] using hx
  have hyN : y ∈ N := by
    have hy := S.infinityDivisionNormalClosure_Qpt_coordinates_mem.2
    change ptY (Genuine.Qpt E S.prime.ℓ) ∈ N at hy
    simpa only [hQ, ptY] using hy
  let ι : N →ₐ[↥S.prime.torsionField] Genuine.Ω E := N.val.restrictScalars _
  have hQN : (E⁄N).toAffine.Nonsingular (⟨x, hxN⟩ : N) ⟨y, hyN⟩ :=
    (Affine.baseChange_nonsingular (W := E) (f := ι) Subtype.val_injective _ _).mp h
  have hGN : (E⁄N).toAffine.Nonsingular
      (⟨Genuine.xG E, S.infinityDivisionNormalClosure_xG_mem⟩ : N)
      ⟨Genuine.yG E, S.infinityDivisionNormalClosure_yG_mem⟩ :=
    (Affine.baseChange_nonsingular (W := E) (f := ι) Subtype.val_injective _ _).mp
      (Genuine.nonsingular_generic E)
  have hmapQ : Affine.Point.map (W' := E) (S := ↥S.prime.torsionField) ι
      (Affine.Point.some _ _ hQN) = Genuine.Qpt E S.prime.ℓ := by rw [hQ]; rfl
  have hmapG : Affine.Point.map (W' := E) (S := ↥S.prime.torsionField) ι
      (Affine.Point.some _ _ hGN) = Genuine.genericPoint E := rfl
  have heff : Genuine.effLevel S.prime.ℓ = S.prime.ℓ :=
    if_neg (Nat.ne_of_gt S.prime.ℓ_prime.pos)
  have hnQN : S.prime.ℓ • Affine.Point.some _ _ hQN = Affine.Point.some _ _ hGN := by
    apply Affine.Point.map_injective (W' := E) (S := ↥S.prime.torsionField) ι
    rw [map_nsmul, hmapQ, hmapG]
    simpa only [Genuine.Qpt, heff] using
      Genuine.nsmul_divSys E S.prime.ℓ S.prime.ℓ_prime.pos
  let σ : N →ₐ[↥S.prime.torsionField] N := τ.toAlgHom.restrictScalars _
  have hσG : Affine.Point.map (W' := E) (S := ↥S.prime.torsionField) σ
      (Affine.Point.some _ _ hGN) = Affine.Point.some _ _ hGN :=
    some_ext (hF _ S.infinityTranslationBaseField_xG_mem)
      (hF _ S.infinityTranslationBaseField_yG_mem)
  have hinv : algebraMap (coordRing (Genuine.xG E)⁻¹ N) N
      (algebraMap (polynomialBase ↥S.prime.torsionField (Genuine.xG E)⁻¹)
        (coordRing (Genuine.xG E)⁻¹ N)
        (polynomialCoordinate (Genuine.xG E)⁻¹)) =
      (⟨Genuine.xG E, S.infinityDivisionNormalClosure_xG_mem⟩ : N)⁻¹ := by
    apply Subtype.ext
    rfl
  have hx0 : (⟨Genuine.xG E, S.infinityDivisionNormalClosure_xG_mem⟩ : N) ≠ 0 := by
    intro hz
    exact (Genuine.transcendental_xG E).ne_zero
      (congrArg (fun a : N => (a : Genuine.Ω E)) hz)
  have key := FiniteInversePrimePoleInertia.inertia_fixes_of_inverse_center
    (Genuine.xG E)⁻¹ S.infinityTranslation_inverseCoordinate_transcendental N E p τ hτ
    S.prime.ℓ S.prime.ℓ_prime.pos
    (S.prime.ℓ_prime.odd_of_ne_two (Nat.ne_of_gt
      ((Nat.lt_succ_self 2).trans_le
        ((Nat.le_succ 3).trans ((Nat.le_succ 4).trans S.prime.five_le)))))
    S.infinityTwoTorsionShift S.infinityTwoTorsionShift_ne_zero
    S.infinityTwoTorsionShift_two_nsmul hx0 hGN hinv hp hσG
    (Affine.Point.some _ _ hQN) hnQN
  have hcoords := Affine.Point.some.inj key
  change τ (⟨x, hxN⟩ : N) = ⟨x, hxN⟩ ∧ τ (⟨y, hyN⟩ : N) = ⟨y, hyN⟩ at hcoords
  change τ ⟨ptX (Genuine.Qpt E S.prime.ℓ),
      S.infinityDivisionNormalClosure_Qpt_coordinates_mem.1⟩ =
      ⟨ptX (Genuine.Qpt E S.prime.ℓ),
        S.infinityDivisionNormalClosure_Qpt_coordinates_mem.1⟩ ∧
    τ ⟨ptY (Genuine.Qpt E S.prime.ℓ),
      S.infinityDivisionNormalClosure_Qpt_coordinates_mem.2⟩ =
      ⟨ptY (Genuine.Qpt E S.prime.ℓ),
        S.infinityDivisionNormalClosure_Qpt_coordinates_mem.2⟩
  simpa only [hQ, ptX, ptY] using hcoords

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
