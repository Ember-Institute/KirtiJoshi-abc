import ArithmeticTeichmullerSpaces.Act1Scene1.WittFractionCoefficientSquare

/-!
source-id: JT-SCENE1-WITT-COMPARISON-DATA
source: Witt functoriality and the fraction-ring universal property.
fidelity: constructs the Witt and ambient equivalences together with their
coefficient and inclusion laws in one abstract coefficient-ring context.
All laws are proved by ofSquare; no caller supplies Witt or ambient laws.
Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1.WittComparisonData

noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {F G I J : Type*} [CommRing F] [CommRing G]

structure Data (E : F ≃+* G) (e : I → J) (f : I → F) (g : J → G) where
  fieldEquiv : WittVector p F ≃+* WittVector p G
  field_coeff : ∀ x n, (fieldEquiv.toEquiv.toFun x).coeff n = E.toEquiv.toFun (x.coeff n)
  inclusion_coeff : ∀ a n,
    (WittVector.mapFun g (WittVector.mapFun e a)).coeff n =
      (fieldEquiv.toEquiv.toFun (WittVector.mapFun f a)).coeff n
  ambientEquiv : FractionRing (WittVector p F) ≃+* FractionRing (WittVector p G)
  ambient_algebraMap : ∀ x,
    ambientEquiv.toEquiv.toFun (algebraMap _ _ x) =
      algebraMap _ _ (fieldEquiv.toEquiv.toFun x)
  ambient_square : ∀ a,
    algebraMap (WittVector p G) (FractionRing (WittVector p G))
        (WittVector.mapFun g (WittVector.mapFun e a)) =
      ambientEquiv.toEquiv.toFun
        (algebraMap (WittVector p F) (FractionRing (WittVector p F))
          (WittVector.mapFun f a))

def ofSquare (E : F ≃+* G) {e : I → J} {f : I → F} {g : J → G}
    (h : ∀ x, g (e x) = E.toEquiv.toFun (f x)) : Data p E e f g where
  fieldEquiv := WittRingEquiv.mapEquiv p E
  field_coeff _ _ := rfl
  inclusion_coeff := WittFractionCoefficientSquare.coeff p E h
  ambientEquiv := fractionRingEquiv (WittRingEquiv.mapEquiv p E)
  ambient_algebraMap := fractionRingEquiv_algebraMap (WittRingEquiv.mapEquiv p E)
  ambient_square := WittFractionCoefficientSquare.ambient_square p E h

end
end JoshiTeich.Act1Scene1.WittComparisonData
