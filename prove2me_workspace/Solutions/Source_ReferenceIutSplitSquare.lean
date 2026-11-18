/-
The square-root descent is `JoshiTeich.ReferenceIut.exists_sq_eq_neg_c₄_mul_c₆`,
the Scene 1 adaptation of Iut/Cor312/ThetaData/SqrtAtBadPlace.lean.
Original revision e4777b2238f45be2e58c00b4d0213c0cb83405b9.
Source snapshot 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompat.Cor312.ThetaData.SqrtAtBadPlace
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateFamily

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField WeierstrassCurve
open scoped Classical

universe u

noncomputable section

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))} {w : FinitePlace ↥K}

local instance (priority := 1100) instDecidableEqSplitSquare : DecidableEq ↥K :=
  fun a b => Classical.propDecidable (a = b)

/-- Rational odd-prime torsion makes `−c₄c₆` a square in the completion at a bad place. -/
theorem exists_sq_eq_neg_c₄_mul_c₆
    (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2)
    (hmult : ∀ v ∈ VBad, ∀ v₀ : FinitePlace F, FinitePlace.LiesOver v₀ v →
      HasMultiplicativeReductionAt E v₀)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (TK : AddSubgroup (curveK E K).toAffine.Point)
    (hTK : TK ≤ AddSubgroup.torsionBy (curveK E K).toAffine.Point ℓ)
    (hcard : ℓ * ℓ ≤ Nat.card ↥TK) (hw : IsBadPlace E K VBad w) :
    ∃ s : localCompletion w, s ^ 2 = emb K w (algebraMap F ↥K (-(E.c₄ * E.c₆))) := by
  exact JoshiTeich.ReferenceIut.exists_sq_eq_neg_c₄_mul_c₆
    E K (VBad := VBad) hVBad hmult hℓ hodd TK hTK hcard (w := w) hw

end

end AbcAdaptation.Reference.Iut
