import Mathlib.Logic.Function.Defs

/-!
source-id: JT-SCENE1-FROBENIUS-COMPLETION-SQUARE
source: Joshi II `se:ff-rings`, Frobenius comparison on completion carriers.
fidelity: lifts a proved carrier naturality law through two observation
maps and their compatibility laws. Only the target observation map must
be injective. All maps are ordinary functions on their original types;
concrete consumers must supply each compatibility law.
Original proof; no reference implementation copied.
boundary: generic function calculation only; no completion construction,
topology, ring structure or period-ring identity is supplied.
-/

namespace JoshiTeich.Act1Scene1.FrobeniusCompletionSquare

theorem commutes {Acomp Bcomp Acarrier Bcarrier : Type*}
    {E : Acarrier → Bcarrier} {Fa : Acarrier → Acarrier}
    {Gb : Bcarrier → Bcarrier}
    (hnat : ∀ a, E (Fa a) = Gb (E a))
    (i : Acomp → Acarrier) (j : Bcomp → Bcarrier)
    (m : Acomp → Bcomp) (F : Acomp → Acomp) (G : Bcomp → Bcomp)
    (hjInjective : Function.Injective j)
    (hi : ∀ x, i (F x) = Fa (i x))
    (hj : ∀ y, j (G y) = Gb (j y))
    (hm : ∀ x, j (m x) = E (i x))
    (x : Acomp) : m (F x) = G (m x) := by
  apply hjInjective
  calc
    j (m (F x)) = E (i (F x)) := hm (F x)
    _ = E (Fa (i x)) := congrArg E (hi x)
    _ = Gb (E (i x)) := hnat (i x)
    _ = Gb (j (m x)) := congrArg Gb (hm x).symm
    _ = j (G (m x)) := (hj (m x)).symm

end JoshiTeich.Act1Scene1.FrobeniusCompletionSquare
