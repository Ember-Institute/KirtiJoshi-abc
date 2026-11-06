import Mathlib.RingTheory.Localization.Away.Basic

/-!
source-id: JT-SCENE1-LOCALIZATION-COMPARISON-SQUARE
source: the universal property of localization away from one element.
fidelity: extends an integral inclusion square through two Away localizations.
The statement is independent of Witt vectors, coefficient certificates, and
the actual/standard geometric carriers.  The only comparison inputs are the
integral square, the induced localization equivalence, and the two invertibility
proofs needed by the Away lifts.
-/

namespace JoshiTeich.Act1Scene1.LocalizationComparisonSquare

noncomputable section

variable {R S Rloc Sloc A B : Type*}
variable [CommRing R] [CommRing S] [CommRing Rloc] [CommRing Sloc]
variable [CommRing A] [CommRing B]
variable [Algebra R Rloc] [Algebra S Sloc]

/--
An integral square extends uniquely across two localizations away from one
element.  The maps `f` and `g` are the integral inclusions into the two
ambient rings; `E` is the ambient equivalence and `L` is the equivalence of
the localized rings.  The hypotheses `hL` and `hbase` are exactly the two
integral squares consumed by the universal property.
-/
theorem awayLift_commutes
    {r : R} {s : S}
    [IsLocalization.Away r Rloc] [IsLocalization.Away s Sloc]
    (e : R ≃+* S)
    (L : Rloc ≃+* Sloc)
    (E : A ≃+* B)
    (f : R →+* A) (g : S →+* B)
    (hr : IsUnit (f r)) (hs : IsUnit (g s))
    (hL : ∀ x : R,
      L (algebraMap R Rloc x) = algebraMap S Sloc (e x))
    (hbase : ∀ x : R, E (f x) = g (e x))
    (x : Rloc) :
    E (IsLocalization.Away.lift r hr x) =
      IsLocalization.Away.lift s hs (L x) := by
  have hsquare :
      E.toRingHom.comp (IsLocalization.Away.lift r hr) =
        (IsLocalization.Away.lift s hs).comp L.toRingHom := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers r)
    ext a
    simp only [RingHom.comp_apply]
    rw [IsLocalization.Away.lift_eq]
    change E (f a) = IsLocalization.Away.lift s hs
      (L (algebraMap R Rloc a))
    rw [hL a, IsLocalization.Away.lift_eq]
    exact hbase a
  exact RingHom.congr_fun hsquare x

end
end JoshiTeich.Act1Scene1.LocalizationComparisonSquare
