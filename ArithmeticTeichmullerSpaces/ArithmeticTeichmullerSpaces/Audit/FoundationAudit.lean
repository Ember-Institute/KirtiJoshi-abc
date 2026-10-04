import ArithmeticTeichmullerSpaces.Act2.Foundation
import Mathlib.Data.Rat.Defs

namespace JoshiTeich

/-! Small compile-time checks for the A0 trust boundary. -/

#check ASTData
example : ASTData → Prop := AST₀
example : ASTData → Prop := FirstAxiom
example : ASTData → Prop := Corollary312

noncomputable def toyAST : ASTData where
  K := ℚ
  fieldStructure := inferInstance
  ossPlaces := {0}
  place := fun _ =>
    { label := 0
      residueDegree := 1
      valuation := fun _ => 1 }
  untilt :=
    { carrier := ℚ
      map := id
      frobenius := id }
  theta :=
    { qParameter := 1
      thetaValue := fun _ => 1
      thetaPilot := {0} }
  packet :=
    { packetIndex := {0}
      coordinate := fun _ => 1
      hullRegion := {0}
      logVolume := 1 }
  height := fun _ => 0
  norm := fun _ => 0
  qNorm := fun _ => 1
  ell := 3
  ellStar := 1

example : AST₀ toyAST := by
  simp [AST₀, toyAST]
  exact ⟨by decide, by change (1 : ℚ) ≠ 0; norm_num⟩

end JoshiTeich
