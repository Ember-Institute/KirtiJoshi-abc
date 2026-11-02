import ArithmeticTeichmullerSpaces.Act1Scene1.WittCoefficientSquare
import ArithmeticTeichmullerSpaces.Act1Scene1.WittRingEquiv
import ArithmeticTeichmullerSpaces.Act1Scene1.FractionRingEquiv

/-!
source-id: JT-SCENE1-WITT-FRACTION-COEFFICIENT-SQUARE
source: Witt-vector functoriality and the fraction-ring universal property.
fidelity: checks the transition from functions to Witt ring equivalences
and fraction-ring equivalences while all coefficient rings are abstract.
Original proofs; no additional comparison hypothesis is introduced.
-/

namespace JoshiTeich.Act1Scene1.WittFractionCoefficientSquare

noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F G I J : Type*} [CommRing F] [CommRing G]
variable (E : F ≃+* G)
variable {e : I → J} {f : I → F} {g : J → G}
variable (h : ∀ x, g (e x) = E.toEquiv.toFun (f x))

include h

theorem coeff (a : WittVector p I) (n : ℕ) :
    (WittVector.mapFun g (WittVector.mapFun e a)).coeff n =
      ((WittRingEquiv.mapEquiv p E).toEquiv.toFun
        (WittVector.mapFun f a)).coeff n :=
  WittCoefficientSquare.coeff p h a n

theorem square (a : WittVector p I) :
    WittVector.mapFun g (WittVector.mapFun e a) =
      (WittRingEquiv.mapEquiv p E).toEquiv.toFun (WittVector.mapFun f a) :=
  WittVector.ext (coeff p E h a)

theorem coeff_forward (a : WittVector p I) (n : ℕ) :
    ((WittRingEquiv.mapEquiv p E).toEquiv.toFun
      (WittVector.mapFun f a)).coeff n =
      (WittVector.mapFun g (WittVector.mapFun e a)).coeff n :=
  (coeff p E h a n).symm

theorem square_forward (a : WittVector p I) :
    (WittRingEquiv.mapEquiv p E).toEquiv.toFun (WittVector.mapFun f a) =
      WittVector.mapFun g (WittVector.mapFun e a) :=
  (square p E h a).symm

theorem ambient_square (a : WittVector p I) :
    algebraMap (WittVector p G) (FractionRing (WittVector p G))
        (WittVector.mapFun g (WittVector.mapFun e a)) =
      (fractionRingEquiv (WittRingEquiv.mapEquiv p E)).toEquiv.toFun
        (algebraMap (WittVector p F) (FractionRing (WittVector p F))
          (WittVector.mapFun f a)) := by
  exact (congrArg (algebraMap (WittVector p G) (FractionRing (WittVector p G)))
    (square p E h a)).trans
      (fractionRingEquiv_algebraMap (WittRingEquiv.mapEquiv p E)
        (WittVector.mapFun f a)).symm

end
end JoshiTeich.Act1Scene1.WittFractionCoefficientSquare
