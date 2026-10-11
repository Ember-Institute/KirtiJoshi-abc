/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/SL2Image.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `a2c25b2edbf5a9cbc30588b466a738b49547b443`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: ports the generic ramification-index divisibility lemma to the
local representation fixed-field contract.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutModEllRepFixedField

/-!
source-id: IUT-COR312-RAMIFICATION-CARDINALITY
source: `refer/iut/Iut/Concrete/SL2Image.lean`,
`EllipticCurveData.ramificationIdx'_dvd_card_gal`.
fidelity: for a finite place of the representation fixed field above a base
place, its relative ramification index divides the finite Galois-group
cardinality. The result is independent of Tate reduction and does not assert
that the representation image contains an element of order `ell`.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.IutCurveModEllRepData

open JoshiTeich.Prologue
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open JoshiTeich.ReferenceIut
open scoped Classical

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F]
variable {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {ell : ℕ} (R : IutCurveModEllRepData F E Fbar ell)

lemma ramificationIdx_dvd_card_gal
    {w : NumberField.FinitePlace F}
    {w' : NumberField.FinitePlace ↥R.torsionField}
    (hw'w : FinitePlace.LiesOver w' w) :
    w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal ∣
      Nat.card (↥R.torsionField ≃ₐ[F] ↥R.torsionField) := by
  haveI : w'.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hw'w
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    w.maximalIdeal.asIdeal (𝓞 ↥R.torsionField)
      (↥R.torsionField ≃ₐ[F] ↥R.torsionField)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ w'.maximalIdeal.asIdeal
    (↥R.torsionField ≃ₐ[F] ↥R.torsionField)] at h
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ w.maximalIdeal.ne_bot]
  exact ⟨(w.maximalIdeal.asIdeal.primesOver (𝓞 ↥R.torsionField)).ncard *
    w.maximalIdeal.asIdeal.inertiaDegIn (𝓞 ↥R.torsionField), by rw [← h]; ring⟩

end

end JoshiTeich.Act1Scene1.IutCurveModEllRepData
