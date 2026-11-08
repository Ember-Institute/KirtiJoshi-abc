import ArithmeticTeichmullerSpaces.Act1Scene1.ActualTateCurveSplitReduction
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.TateStructure

/-!
source-id: JT-SCENE1-TATE-STRUCTURE-LOCAL-SPLIT-MODEL
source: Joshi III `ss:theta-data-fixing2` and `ss:val-sets-defn`;
Mathlib's minimal-model requirement for split multiplicative reduction.
fidelity: consumes an actual `TateStructure W` and uses its supplied local
coordinate change to exhibit a split multiplicative model of W.
boundary: the conclusion is existential over local changes. It does not imply
that W itself is minimal, or identify the model with a global change over the
number field. Original proof; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1.TateReduction

open WeierstrassCurve NumberField IsDiscreteValuationRing
open JoshiTeich.ReferenceIut

noncomputable section

variable {F : Type*} [Field F] [NumberField F]
variable (w : FinitePlace F)
variable {W : WeierstrassCurve (localCompletion w)}

local notation "R" => w.maximalIdeal.adicCompletionIntegers F
local notation "K" => localCompletion w

/-- A supplied Tate structure gives a split multiplicative local model after
its own local coordinate change. -/
theorem exists_local_split_model_of_tateStructure (S : TateStructure W)
    (h12 : (12 : localCompletion w) ≠ 0) :
    ∃ C : VariableChange K, (C • W).HasSplitMultiplicativeReduction R := by
  refine ⟨S.C, ?_⟩
  rw [S.hC]
  exact tateCurve_hasSplitMultiplicativeReduction w S.t h12

/-- The local existence predicate consumed by the actual Tate structure. -/
def HasLocalSplitMultiplicativeReduction (W : WeierstrassCurve K) : Prop :=
  ∃ C : VariableChange K, (C • W).HasSplitMultiplicativeReduction R

theorem tateStructure_implies_localSplitPredicate (S : TateStructure W)
    (h12 : (12 : localCompletion w) ≠ 0) :
    HasLocalSplitMultiplicativeReduction w W :=
  exists_local_split_model_of_tateStructure w S h12

end
end JoshiTeich.Act1Scene1.TateReduction
