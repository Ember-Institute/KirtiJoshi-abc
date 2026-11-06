import ArithmeticTeichmullerSpaces.Act1Scene1.WittFractionCoefficientSquare

/-!
source-id: JT-SCENE1-WITT-FRACTION-AMBIENT-SQUARE
source: the abstract Witt coefficient and fraction-ring comparison laws.
fidelity: packages the symmetric ambient square as a reusable theorem so a
concrete carrier only applies an already elaborated generic result.
Original proof; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1.WittFractionAmbientSquare

noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F G I J : Type*} [CommRing F] [CommRing G]
variable (E : F ≃+* G)
variable {e : I → J} {f : I → F} {g : J → G}
variable (h : ∀ x, g (e x) = E.toEquiv.toFun (f x))

include h

theorem map_algebraMap (a : WittVector p I) :
    (fractionRingEquiv (WittRingEquiv.mapEquiv p E)).toEquiv.toFun
        (algebraMap (WittVector p F) (FractionRing (WittVector p F))
          (WittVector.mapFun f a)) =
      algebraMap (WittVector p G) (FractionRing (WittVector p G))
        (WittVector.mapFun g (WittVector.mapFun e a)) :=
  (WittFractionCoefficientSquare.ambient_square p E h a).symm

end
end JoshiTeich.Act1Scene1.WittFractionAmbientSquare
