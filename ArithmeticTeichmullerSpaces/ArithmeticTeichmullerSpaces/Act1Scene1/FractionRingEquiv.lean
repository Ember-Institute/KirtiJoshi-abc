import Mathlib.RingTheory.Localization.FractionRing

/-!
source-id: JT-SCENE1-FRACTION-RING-EQUIV
source: Mathlib IsFractionRing.ringEquivOfRingEquiv and its algebraMap law.
fidelity: fixes the fraction-ring construction in an abstract ring context
before a concrete Witt equivalence is supplied. Original wrapper proofs;
no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

noncomputable section

def fractionRingEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : FractionRing A ≃+* FractionRing B :=
  IsFractionRing.ringEquivOfRingEquiv e

theorem fractionRingEquiv_algebraMap {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (x : A) :
    fractionRingEquiv e (algebraMap A (FractionRing A) x) =
      algebraMap B (FractionRing B) (e x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap e x

end
end JoshiTeich.Act1Scene1
