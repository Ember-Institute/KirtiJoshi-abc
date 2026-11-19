import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateFamily
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompat.Cor312.ThetaData.TateFamilyGalois

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField
open scoped Classical Valued

universe u

noncomputable section

section Local

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
variable {E : WeierstrassCurve k}

/-- Read the same parametrized Tate structure in the main project's reference library. -/
private def TateStructure.toJoshi (S : TateStructure E) :
    JoshiTeich.ReferenceIut.TateStructure E where
  t := ⟨S.t.q, S.t.norm_lt_one⟩
  C := S.C
  hC := S.hC
  iso := S.iso
  iso_x := S.iso_x
  iso_y := S.iso_y

end Local

section Family

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]
variable (ℓ : ℕ) (VBad : Set (FinitePlace ↥(fieldOfModuli F E)))

/-- Assemble the indexed Tate structures using the Galois equivariance of the graph line and
the canonical generators proved in `Iut/Cor312/ThetaData/TateFamilyGalois.lean`. -/
def TateFamily.ofStructures
    (S : ∀ w : FinitePlace ↥K, IsBadPlace E K VBad w → TateStructure (curveKw E K w)) :
    TateFamily E K ℓ VBad := by
  let T := JoshiTeich.ReferenceIut.TateFamily.ofStructures E K ℓ VBad
    (fun w hw => (S w hw).toJoshi)
  refine { S := S, graphLine_galPlace := ?_, isCanonical_galPlace := ?_ }
  · intro w hw σ
    exact T.graphLine_galPlace w hw σ
  · intro w hw σ R
    exact T.isCanonical_galPlace w hw σ R

end Family

end

end AbcAdaptation.Reference.Iut
