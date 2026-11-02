import Mathlib.RingTheory.WittVector.Basic

/-!
source-id: JT-SCENE1-WITT-COEFFICIENT-SQUARE
source: coefficientwise functoriality of WittVector.mapFun.
fidelity: lifts a commuting square of functions to Witt coefficients. No
ring instances are needed at this interface. Original proofs.
-/

namespace JoshiTeich.Act1Scene1.WittCoefficientSquare

theorem coeff (p : ℕ) {I J F G : Type*}
    {e : I → J} {E : F → G} {f : I → F} {g : J → G}
    (h : ∀ x, g (e x) = E (f x)) (a : WittVector p I) (n : ℕ) :
    (WittVector.mapFun g (WittVector.mapFun e a)).coeff n =
      (WittVector.mapFun E (WittVector.mapFun f a)).coeff n :=
  h (a.coeff n)

theorem square (p : ℕ) {I J F G : Type*}
    {e : I → J} {E : F → G} {f : I → F} {g : J → G}
    (h : ∀ x, g (e x) = E (f x)) (a : WittVector p I) :
    WittVector.mapFun g (WittVector.mapFun e a) =
      WittVector.mapFun E (WittVector.mapFun f a) :=
  WittVector.ext (coeff p h a)

end JoshiTeich.Act1Scene1.WittCoefficientSquare
