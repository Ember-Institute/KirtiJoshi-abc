import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoCompletion

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-RHO-SOURCE-EMBEDDING
source: Joshi II `se:ff-rings`, the bounded source inside a fixed-rho completion.
fidelity: records the underlying functions of the original standard source
copy and completion inclusion. Only p and rho enter these formulas.
Original proof; Scene1/Derived; no paper B identity is asserted.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoCompletion

noncomputable section
variable (p : ℕ) [Fact p.Prime]

theorem sourceEquiv_apply (ρ : Radius) (x : PadicBoundedWittLocalization.Ring p) :
    sourceEquiv p ρ x = (show Source p ρ from x) := rfl

theorem inclusion_apply (ρ : Radius) (x : PadicBoundedWittLocalization.Ring p) :
    inclusion p ρ x =
      ((show Source p ρ from x) : UniformSpace.Completion (Source p ρ)) := rfl

def inclusionFun (ρ : Radius) (x : PadicBoundedWittLocalization.Ring p) :
    Completed p ρ := ((show Source p ρ from x) : UniformSpace.Completion (Source p ρ))

theorem inclusion_eq_inclusionFun (ρ : Radius) :
    (inclusion p ρ : PadicBoundedWittLocalization.Ring p → Completed p ρ) =
      inclusionFun p ρ := rfl

end
end JoshiTeich.Act1Scene1.PadicWittRhoCompletion
