/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/SL2Image.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `47ef99c97945984ea799ee2333fcf920abecdae4`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: ports the image-cardinality and SL2-generation tail with
ramification divisibility retained as an explicit local source.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutRootClassRamification
import ArithmeticTeichmullerSpaces.Act1Scene1.IutModEllRepCyclicSubgroup
import ArithmeticTeichmullerSpaces.Act1Scene1.IutSL2Generation

/-!
source-id: IUT-COR312-SL2-IMAGE-BRIDGE
source: `refer/iut/Iut/Concrete/SL2Image.lean`,
`EllipticCurveData.prime_dvd_card_range` and `sl_le_range_of`.
fidelity: an explicit family of local ramification divisibility proofs gives
`ell ∣ Nat.card (rep.range)`. Cauchy's theorem then supplies an order-`ell`
element, and the independent stable-line and transvection lemmas yield the
`SL₂` image inclusion. Local Tate parameter alignment and ramification
divisibility remain explicit hypotheses of the bridge.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.IutCurveModEllRepData

open JoshiTeich.Prologue
open NumberField Matrix
open JoshiTeich.ReferenceIut
open JoshiTeich.Act1Scene1
open scoped Classical MatrixGroups

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F]
variable {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {ell : ℕ} (R : IutCurveModEllRepData F E Fbar ell)

lemma prime_dvd_card_range_of_ramification
    (hp : ell.Prime)
    (hP5 : ∃ w : FinitePlace F,
      residueChar w ≠ 2 ∧ residueChar w ≠ ell)
    (hDvd : ∀ (w : FinitePlace F) (h2 : residueChar w ≠ 2)
      (hwℓ : residueChar w ≠ ell)
      (w' : FinitePlace ↥R.torsionField), FinitePlace.LiesOver w' w →
      ell ∣ w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal) :
    ell ∣ Nat.card R.rep.range := by
  obtain ⟨w, h2, hwℓ⟩ := hP5
  obtain ⟨w', hw'w⟩ :=
    JoshiTeich.ReferenceIut.FinitePlace.exists_liesOver
      (K := ↥R.torsionField) w
  rw [R.card_range]
  exact (hDvd w h2 hwℓ w' hw'w).trans (R.ramificationIdx_dvd_card_gal hw'w)

theorem sl_le_range_of_prime_dvd_card
    (hp : ell.Prime)
    (hCard : ell ∣ Nat.card R.rep.range)
    (hP4 : ¬ IutHasCyclicSubgroup E Fbar ell)
    (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ell)) :
    A.toGL ∈ R.rep.range := by
  letI : Fact ell.Prime := ⟨hp⟩
  obtain ⟨T, hT⟩ := exists_prime_orderOf_dvd_card' ell hCard
  rw [← Subgroup.orderOf_coe] at hT
  obtain ⟨hT1, hT2⟩ := IutSL2.transvection_of_orderOf
    (T : GL (Fin 2) (ZMod ell)) hT
  exact IutSL2.toGL_mem_of_transvection R.rep.range T.2 hT1 hT2
    (R.exists_mulVec_ne_smul_of_not_hasCyclicSubgroup hP4) A

theorem sl_le_range_of_ramification
    (hp : ell.Prime)
    (hP5 : ∃ w : FinitePlace F,
      residueChar w ≠ 2 ∧ residueChar w ≠ ell)
    (hDvd : ∀ (w : FinitePlace F) (h2 : residueChar w ≠ 2)
      (hwℓ : residueChar w ≠ ell)
      (w' : FinitePlace ↥R.torsionField), FinitePlace.LiesOver w' w →
      ell ∣ w.maximalIdeal.asIdeal.ramificationIdx' w'.maximalIdeal.asIdeal)
    (hP4 : ¬ IutHasCyclicSubgroup E Fbar ell)
    (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ell)) :
    A.toGL ∈ R.rep.range := by
  exact R.sl_le_range_of_prime_dvd_card hp
    (R.prime_dvd_card_range_of_ramification hp hP5 hDvd) hP4 A

end

end JoshiTeich.Act1Scene1.IutCurveModEllRepData
