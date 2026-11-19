namespace Iut

open NumberField IsDedekindDomain WeierstrassCurve IntermediateField

section Reduction

variable {F : Type*} [Field F] [NumberField F] (E : WeierstrassCurve F)

def HasGoodReductionAt (w : FinitePlace F) : Prop :=
  ∃ C : VariableChange F,
    ((C • E).baseChange (w.maximalIdeal.adicCompletion F)).HasGoodReduction
      (w.maximalIdeal.adicCompletionIntegers F)

def HasMultiplicativeReductionAt (w : FinitePlace F) : Prop :=
  ∃ C : VariableChange F,
    ((C • E).baseChange (w.maximalIdeal.adicCompletion F)).HasMultiplicativeReduction
      (w.maximalIdeal.adicCompletionIntegers F)

def HasStableReductionAt (w : FinitePlace F) : Prop :=
  HasGoodReductionAt E w ∨ HasMultiplicativeReductionAt E w

end Reduction

section FieldOfModuli

variable (F : Type*) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]

noncomputable def fieldOfModuli : IntermediateField ℚ F := ℚ⟮E.j⟯

instance : FiniteDimensional ℚ ↥(fieldOfModuli F E) :=
  Module.Finite.left ℚ ↥(fieldOfModuli F E) F

instance : NumberField ↥(fieldOfModuli F E) where

def IsGaloisOfDegreePrimeTo (ℓ : ℕ) : Prop :=
  IsGalois ↥(fieldOfModuli F E) F ∧ Nat.Coprime (Module.finrank ↥(fieldOfModuli F E) F) ℓ

end FieldOfModuli

section Conditions

variable (F : Type*) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]

variable (Fbar : Type*) [Field Fbar] [Algebra F Fbar]

open scoped Classical in

def SixTorsionRational : Prop :=
  ∀ P ∈ AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) 6,
    P ∈ (Affine.Point.baseChange (W' := E) F Fbar).range
