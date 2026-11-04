import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittComparison

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-BOUNDED-WITT-MAP-LAWS
source: Joshi II `se:ff-rings`, the bounded Witt period subring and the
proved actual-to-standard bounded ring equivalence.
fidelity: proves bijectivity of the saved function on the original bounded
carriers from its proved equality with the original ring equivalence.
The maps, standard contraction, carriers and norms remain unchanged.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; completion, diagonal and paper identities are
separate obligations. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeMapLaws : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem ringFun_surjective : Function.Surjective (ringFun D w) := by
  intro y
  obtain ⟨x, hx⟩ := (ringEquiv D w).surjective y
  exact ⟨x, (ringEquiv_apply_eq_ringFun D w x).symm.trans hx⟩

theorem ringFun_injective : Function.Injective (ringFun D w) := by
  intro x y h
  apply (ringEquiv D w).injective
  exact (ringEquiv_apply_eq_ringFun D w x).trans
    (h.trans (ringEquiv_apply_eq_ringFun D w y).symm)

end
end JoshiTeich.Act1Scene1.InitialThetaPadicBoundedWittComparison
