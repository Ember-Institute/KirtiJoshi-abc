import Solutions.Source_ReferenceIutCor312RepresentativePadicProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicPaperLog
import ArithmeticTeichmullerSpaces.Act1Scene1.AlgebraicallyClosedFontaine

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1 JoshiTeich.Prologue.Arithmetic

noncomputable section

local instance representativeCrystallineCompletionPrime {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) : Fact (residueChar s).Prime :=
  LocalCompletion.selectedPrime s

section Completion

variable {K : Type*} [Field K] [NumberField K] (s : FinitePlace K)

/-- Map the original Kummer algebraic closure into the standard completed field. -/
def algebraicClosureInPadicComplex :
    AlgebraicClosure (LocalCompletion.completionAt K s) →+* PadicComplex (residueChar s) :=
  (UniformSpace.Completion.coeRingHom : PadicAlgCl (residueChar s) →+*
    PadicComplex (residueChar s)).comp (LocalCompletion.padicAlgClEquiv s).toRingHom

theorem algebraicClosureInPadicComplex_algebraMap (x : LocalCompletion.completionAt K s) :
    algebraicClosureInPadicComplex s
      (algebraMap (LocalCompletion.completionAt K s)
        (AlgebraicClosure (LocalCompletion.completionAt K s)) x) =
      completionInPadicComplex s x := rfl

end Completion

/-- Multiplication by `p*` introduces an integral multiple of `p` at every prime. -/
theorem paperPrincipalUnit_integral {C : Type*} [NormedField C] [IsUltrametricDist C]
    (p : ℕ) (x : C) (hx : ‖x‖ ≤ 1) :
    ‖1 + (LocalPadicLog.paperScale p : C) * x‖ ≤ 1 ∧
      ∃ r : LocalGeometricFontaine.integerRing C,
        1 + (LocalPadicLog.paperScale p : C) * x = 1 + (p : C) * (r : C) := by
  let d : ℕ := if p = 2 then 2 else 1
  have hscale : LocalPadicLog.paperScale p = p * d := by
    by_cases hp : p = 2 <;> simp [LocalPadicLog.paperScale, d, hp]
  have hd : ‖(d : C) * x‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hx).trans
      (IsUltrametricDist.norm_natCast_le_one C d)
  have hvalue : 1 + (LocalPadicLog.paperScale p : C) * x =
      1 + (p : C) * ((d : C) * x) := by
    rw [hscale, Nat.cast_mul, mul_assoc]
  refine ⟨?_, ⟨⟨_, (LocalGeometricFontaine.mem_integerRing C _).mpr hd⟩, hvalue⟩⟩
  rw [hvalue]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) ?_)
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hd).trans
    (IsUltrametricDist.norm_natCast_le_one C p)

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
