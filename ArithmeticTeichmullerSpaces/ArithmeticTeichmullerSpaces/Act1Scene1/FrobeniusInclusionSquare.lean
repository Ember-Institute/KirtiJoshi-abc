import Mathlib.Logic.Function.Defs

/-!
source-id: JT-SCENE1-FROBENIUS-INCLUSION-SQUARE
source: Joshi II `se:ff-rings`, Frobenius on the dense bounded subring.
fidelity: composes a bounded commutation law, inclusion laws and an
injective observation map. All functions and laws are explicit parameters;
concrete consumers must discharge them on their original carriers.
Original proof; no reference implementation copied.
boundary: generic function calculation only; no period-ring identity supplied.
-/

namespace JoshiTeich.Act1Scene1.FrobeniusInclusionSquare

theorem commutes {S T A B P : Type*}
    {e : S → T} {f : S → S} {q : T → T}
    (hnat : ∀ s, e (f s) = q (e s))
    (i : S → A) (E : A → B) (F : A → A) (G : B → B)
    (j : B → P) (k : T → P) (g : P → P)
    (hj : Function.Injective j)
    (hF : ∀ s, F (i s) = i (f s))
    (hE : ∀ s, j (E (i s)) = k (e s))
    (hG : ∀ b, j (G b) = g (j b))
    (hk : ∀ t, g (k t) = k (q t))
    (s : S) : E (F (i s)) = G (E (i s)) := by
  apply hj
  calc
    j (E (F (i s))) = k (e (f s)) :=
      (congrArg (fun a => j (E a)) (hF s)).trans (hE (f s))
    _ = k (q (e s)) := congrArg k (hnat s)
    _ = j (G (E (i s))) :=
      ((hG (E (i s))).trans ((congrArg g (hE s)).trans (hk (e s)))).symm

end JoshiTeich.Act1Scene1.FrobeniusInclusionSquare
