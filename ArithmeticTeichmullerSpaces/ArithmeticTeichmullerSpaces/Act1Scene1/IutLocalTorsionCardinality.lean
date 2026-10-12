/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/SL2Image.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `47ef99c97945984ea799ee2333fcf920abecdae4`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: ports the global-to-local Tate torsion cardinality lower bound
to the local representation fixed-field contract.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutRamificationCardinality
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompat.Cor312.ThetaData.TateFamilyOfTorsion

/-!
source-id: IUT-COR312-LOCAL-TORSION-CARDINALITY
source: `refer/iut/Iut/Concrete/SL2Image.lean`,
`EllipticCurveData.card_torsion_curveKw_ge`.
fidelity: injects the fixed-field global `ell`-torsion into the local
completion Tate torsion at a finite place. The theorem only supplies the
cardinality lower bound needed by the residue/root-class argument; it does
not construct a Tate structure or a root class.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.IutCurveModEllRepData

open JoshiTeich.Prologue
open NumberField WeierstrassCurve
open JoshiTeich.ReferenceIut
open JoshiTeich.ReferenceIut.Anabelian
open scoped Classical

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F]
variable {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {ell : ℕ} (R : IutCurveModEllRepData F E Fbar ell)

local instance (priority := 1100) instDecidableEqTorsionFieldLocal :
    DecidableEq ↥R.torsionField :=
  fun a b => Classical.propDecidable (a = b)

lemma card_torsion_curveKw_ge
    (w' : FinitePlace ↥R.torsionField)
    [Finite ↥(TateStructure.torsion ell
      (curveKw E R.torsionField w'))] :
    ell * ell ≤ Nat.card ↥(TateStructure.torsion ell
      (curveKw E R.torsionField w')) := by
  let f : ↥R.TK →+
      ↥(TateStructure.torsion ell (curveKw E R.torsionField w')) :=
    ((pointMap (curveK E R.torsionField) (emb R.torsionField w')).domRestrict R.TK).codRestrict _
      (fun P => by
        rw [AddSubgroup.torsionBy.nsmul_iff]
        have hP := AddSubgroup.torsionBy.nsmul_iff.mp P.2
        rw [← map_nsmul]
        have hP' : ell • P = 0 := Subtype.ext hP
        rw [hP', map_zero])
  have hf : Function.Injective f := fun P P' h => by
    apply Subtype.ext
    apply pointMap_injective (curveK E R.torsionField) (emb R.torsionField w')
    have h' := congrArg Subtype.val h
    simpa only [f, AddMonoidHom.codRestrict_apply, AddMonoidHom.domRestrict_apply] using h'
  calc
    ell * ell = Nat.card ↥R.TK := by rw [R.card_torsionBy_EK, sq]
    _ ≤ _ := Nat.card_le_card_of_injective f hf

end

end JoshiTeich.Act1Scene1.IutCurveModEllRepData
