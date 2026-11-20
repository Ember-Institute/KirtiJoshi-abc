/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Anabelian/Genuine/Homs.lean and Iut/Anabelian/Genuine/Core.lean.
The maps and their closed-point multiplicities are on the Scene1 normalization rings.
-/
import Solutions.Source_ReferenceIutCanLiftPresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.AffineOrbicurvePresentationCategory
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineNormalizationSquareRamification
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Model

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve JoshiTeich.Act1Scene1
open JoshiTeich.ReferenceIut.Anabelian (Orbicurve)
open JoshiTeich.ReferenceIut.Anabelian.Genuine
open FunctionFieldNormalization AffineOrbicurvePresentation
open scoped Classical IntermediateField.algebraAdjoinAdjoin

universe u

noncomputable section

private theorem ramificationIndex_mul_multiplicity_of_square
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
    {A B C D : IntermediateField (rationalBase k t) Ω}
    [FiniteDimensional (rationalBase k t) B] [Algebra.IsSeparable (rationalBase k t) B]
    [FiniteDimensional (rationalBase k t) C] [Algebra.IsSeparable (rationalBase k t) C]
    (ht : Transcendental k t) (hAB : A ≤ B) (hAC : A ≤ C) (hBD : B ≤ D) (hCD : C ≤ D)
    (mA : Ideal (coordRing t A) → ℕ) (mC : Ideal (coordRing t C) → ℕ)
    (hA : ∀ p : Ideal (coordRing t B), p.IsMaximal →
      ramificationIndex hAB p = mA (p.comap (ringMap hAB)))
    (hC : ∀ q : Ideal (coordRing t D), q.IsMaximal →
      ramificationIndex hCD q = mC (q.comap (ringMap hCD)))
    (hBD_one : ∀ q : Ideal (coordRing t D), q.IsMaximal → ramificationIndex hBD q = 1)
    (w : Ideal (coordRing t C)) (hw : w.IsMaximal) :
    ramificationIndex hAC w * mC w = mA (w.comap (ringMap hAC)) := by
  obtain ⟨q, hq, hqw⟩ := normalization_exists_maximal_over hCD w hw
  let p := q.comap (ringMap hBD)
  have hp : p.IsMaximal := normalization_comap_isMaximal hBD q hq
  have hcomap : p.comap (ringMap hAB) = w.comap (ringMap hAC) := by
    exact (show p.comap (ringMap hAB) = (q.comap (ringMap hCD)).comap (ringMap hAC) from rfl).trans
      (congrArg (fun v : Ideal (coordRing t C) => v.comap (ringMap hAC)) hqw)
  have hSquare := ramificationIndex_square ht hAB hAC hBD hCD q
  rw [hqw, hBD_one q hq, mul_one] at hSquare
  have hMult : ramificationIndex hCD q = mC w := (hC q hq).trans (congrArg mC hqw)
  exact (congrArg (fun e => ramificationIndex hAC w * e) hMult.symm).trans
    (hSquare.trans ((hA p hp).trans (congrArg mA hcomap)))

variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

private theorem normalizationField_le_of_level {n ℓ ℓ' : ℕ} (hn : 0 < n)
    (hmul : n * ℓ' = ℓ) {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M')
    {pm pm' : Bool} (hpm : pm = true → pm' = true) :
    normalizationField E ℓ' M' pm' ≤ normalizationField E ℓ M pm :=
  rebaseField_mono (baseField_eq_xLine E) (stabilizerField_le_of_cover E hn hmul hM hpm)

private theorem unsignedCover_ramificationIndex {ℓ ℓ' : ℕ}
    {M M' : AddSubgroup E.toAffine.Point}
    (h : normalizationField E ℓ' M' false ≤ normalizationField E ℓ M false)
    (w : Ideal (coverCoordinateRing E ℓ M false)) (hw : w.IsMaximal) :
    ramificationIndex h w = 1 := by
  have hTower : ramificationIndex (normalization_base_unsigned_le E ℓ M) w =
      ramificationIndex (normalization_base_unsigned_le E ℓ' M') (w.comap (ringMap h)) *
        ramificationIndex h w :=
    ramificationIndex_tower (transcendental_xG E) (normalization_base_unsigned_le E ℓ' M') h w
  have hUpper : ramificationIndex (normalization_base_unsigned_le E ℓ M) w = 1 :=
    unsignedNormalization_ramificationIdx_one E ℓ M w hw
  have hLower :
      ramificationIndex (normalization_base_unsigned_le E ℓ' M') (w.comap (ringMap h)) = 1 :=
    unsignedNormalization_ramificationIdx_one E ℓ' M' _
      (normalization_comap_isMaximal h w hw)
  calc
    ramificationIndex h w = 1 * ramificationIndex h w := (one_mul _).symm
    _ = _ := congrArg (fun e => e * ramificationIndex h w) hLower.symm
    _ = _ := hTower.symm
    _ = 1 := hUpper

private theorem signedNormalizationCover_index (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point)
    (q : Ideal (coverCoordinateRing E ℓ M false)) (hq : q.IsMaximal) :
    ramificationIndex (normalizationField_signed_le_unsigned E ℓ M) q =
      (normalizationPresentation E ℓ M true).mult
        (q.comap (ringMap (normalizationField_signed_le_unsigned E ℓ M))) := by
  have hRam := (signedNormalizationCover E ℓ M).ramification q hq
  exact (mul_one _).symm.trans hRam

private def coverOfFieldInclusion {ℓ ℓ' : ℕ} {M M' : AddSubgroup E.toAffine.Point}
    {pm pm' : Bool} (h : normalizationField E ℓ' M' pm' ≤ normalizationField E ℓ M pm)
    (hRam : ∀ w : Ideal (coverCoordinateRing E ℓ M pm), w.IsMaximal →
      ramificationIndex h w * (normalizationPresentation E ℓ M pm).mult w =
        (normalizationPresentation E ℓ' M' pm').mult (w.comap (ringMap h))) :
    Cover (normalizationPresentation E ℓ M pm) (normalizationPresentation E ℓ' M' pm') where
  f := ringMap h
  injective := ringMap_injective h
  isIntegral := ringMap_isIntegral h
  ramification := hRam

private def normalizationLevelCover {n ℓ ℓ' : ℕ} (hn : 0 < n) (hmul : n * ℓ' = ℓ)
    {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M')
    {pm pm' : Bool} (hpm : pm = true → pm' = true) :
    { f : Cover (normalizationPresentation E ℓ M pm) (normalizationPresentation E ℓ' M' pm') //
      ∃ h : normalizationField E ℓ' M' pm' ≤ normalizationField E ℓ M pm, f.f = ringMap h } := by
  let hUnsigned : normalizationField E ℓ' M' false ≤ normalizationField E ℓ M false :=
    normalizationField_le_of_level E hn hmul hM (fun hp => False.elim (Bool.false_ne_true hp))
  cases pm with
  | false =>
    let f : Cover (normalizationPresentation E ℓ M false)
        (normalizationPresentation E ℓ' M' false) :=
      coverOfFieldInclusion E hUnsigned (fun w hw =>
        (mul_one _).trans (unsignedCover_ramificationIndex E hUnsigned w hw))
    cases pm' with
    | false => exact ⟨f, ⟨hUnsigned, rfl⟩⟩
    | true =>
      let h := (normalizationField_signed_le_unsigned E ℓ' M').trans hUnsigned
      exact ⟨f.comp (signedNormalizationCover E ℓ' M'), ⟨h, AlgHom.ext fun _ => rfl⟩⟩
  | true =>
    cases pm' with
    | false => exact False.elim (Bool.false_ne_true (hpm rfl))
    | true =>
      let hSigned := normalizationField_le_of_level E hn hmul hM hpm
      let f := coverOfFieldInclusion E hSigned
          (ramificationIndex_mul_multiplicity_of_square (transcendental_xG E)
            (normalizationField_signed_le_unsigned E ℓ' M') hSigned hUnsigned
            (normalizationField_signed_le_unsigned E ℓ M)
            (normalizationPresentation E ℓ' M' true).mult (normalizationPresentation E ℓ M true).mult
            (signedNormalizationCover_index E ℓ' M') (signedNormalizationCover_index E ℓ M)
            (unsignedCover_ramificationIndex E hUnsigned))
      exact ⟨f, ⟨hSigned, rfl⟩⟩

/-- The normalized affine cover associated to a cover of model orbicurves. -/
def normalizationCoverOfModelCover {X Y : Orbicurve k} (c : Orbicurve.Cover X Y) :
    Cover (normalizationPresentation X.E X.level X.M X.pm)
      (normalizationPresentation Y.E Y.level Y.M Y.pm) := by
  cases X with | @mk W hW ℓ M pm =>
  cases Y with | @mk W' hW' ℓ' M' pm' =>
  obtain ⟨h, n, hn, hmul, hM, hpm⟩ := c
  change W = W' at h
  subst h
  exact (normalizationLevelCover W hn hmul hM hpm).val

/-- Over the same elliptic curve, the map of the model cover is the ambient field inclusion. -/
theorem normalizationCoverOfModelCover_eq_ringMap {n ℓ ℓ' : ℕ} (hn : 0 < n) (hmul : n * ℓ' = ℓ)
    {M M' : AddSubgroup E.toAffine.Point} (hM : ∀ P ∈ M, n • P ∈ M')
    {pm pm' : Bool} (hpm : pm = true → pm' = true) :
    ∃ h : normalizationField E ℓ' M' pm' ≤ normalizationField E ℓ M pm,
      (normalizationCoverOfModelCover (X := ⟨E, ℓ, M, pm⟩) (Y := ⟨E, ℓ', M', pm'⟩)
        ⟨rfl, n, hn, hmul, hM, hpm⟩).f = ringMap h :=
  (normalizationLevelCover E hn hmul hM hpm).property

end

end AbcAdaptation.Reference.Iut.Anabelian
