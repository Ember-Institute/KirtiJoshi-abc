/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/SL2Image.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `a2c25b2edbf5a9cbc30588b466a738b49547b443`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: assembles explicit local Tate witnesses with the
ramification-to-image bridge; no Tate-family source is hidden in the adapter.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutSL2ImageBridge

/-!
source-id: IUT-COR312-SL2-IMAGE-SOURCE-BRIDGE
source: `refer/iut/Iut/Concrete/SL2Image.lean`,
`EllipticCurveData.prime_dvd_card_range` and `sl_le_range_of`.
fidelity: the local Tate witness package supplies the parameter, uniformizer,
Tate structure, q-parameter alignment, torsion-cardinality bound, and
coprimality certificate used by the root-class lemma. The existing image bridge
then supplies Cauchy's theorem and the independent `SL₂` generation argument.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.IutCurveModEllRepData

open JoshiTeich.Prologue
open NumberField Matrix WeierstrassCurve TateCurvesTheta
open JoshiTeich.ReferenceIut
open JoshiTeich.Act1Scene1
open scoped Classical MatrixGroups

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F]
variable {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {ell : ℕ} (R : IutCurveModEllRepData F E Fbar ell)

/-- A local Tate source package sufficient to run the root-class and image argument.
Every field remains an explicit source obligation for a later `InitialThetaData`
instantiation. -/
def LocalTateImageSource : Prop :=
  ∀ (w : FinitePlace F) (h2 : residueChar w ≠ 2)
    (hwℓ : residueChar w ≠ ell)
    (w' : FinitePlace ↥R.torsionField)
    (hw'w : FinitePlace.LiesOver w' w),
    ∃ (t : TateParameter (localCompletion w)) (π : localCompletion w),
      ∃ (hπ : IsUniformizer π),
      ∃ (S : TateStructure (curveKw E R.torsionField w')),
        S.t.q = iutEmbedCompletion hw'w (t.q) ∧
        ell * ell ≤ Nat.card ↥(TateStructure.torsion ell
          (curveKw E R.torsionField w')) ∧
        ¬ ell ∣ (t.toOrdered hπ).orderNat

theorem prime_dvd_card_range_of_local_tate
    (hp : ell.Prime)
    (hP5 : ∃ w : FinitePlace F,
      residueChar w ≠ 2 ∧ residueChar w ≠ ell)
    (hSource : LocalTateImageSource R) :
    ell ∣ Nat.card R.rep.range := by
  unfold LocalTateImageSource at hSource
  apply R.prime_dvd_card_range_of_ramification hp hP5
  intro w h2 hwℓ w' hw'w
  obtain ⟨t, π, hπ, S, hq, hcard, hcop⟩ := hSource w h2 hwℓ w' hw'w
  exact R.prime_dvd_ramificationIdx_of_tate hp hw'w t hπ S hq hcard hcop

theorem sl_le_range_of_local_tate
    (hp : ell.Prime)
    (hP5 : ∃ w : FinitePlace F,
      residueChar w ≠ 2 ∧ residueChar w ≠ ell)
    (hSource : LocalTateImageSource R)
    (hP4 : ¬ IutHasCyclicSubgroup E Fbar ell)
    (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ell)) :
    A.toGL ∈ R.rep.range := by
  exact R.sl_le_range_of_prime_dvd_card hp
    (R.prime_dvd_card_range_of_local_tate hp hP5 hSource) hP4 A

end

end JoshiTeich.Act1Scene1.IutCurveModEllRepData
