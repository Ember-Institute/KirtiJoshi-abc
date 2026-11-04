import Mathlib.RingTheory.Localization.Defs

/-!
source-id: JT-SCENE1-LOCALIZATION-FROBENIUS-NATURALITY
source: Joshi II `se:ff-rings`, functorial Frobenius on bounded Witt
localizations; Mathlib IsLocalization.ringHom_ext.
fidelity: proves commutation of three original ring maps by checking it on
the original integral source. Integral functions are left unbundled, and
all inclusion and commutation premises are explicit. The concrete consumer
must discharge them from its existing maps. Original proof; no reference
implementation copied. No norm, completion or actual data is used here.
boundary: this generic implication supplies no actual source law or paper identity.
-/

namespace JoshiTeich.Act1Scene1.LocalizationFrobeniusNaturality

theorem commutes
    {A B L T : Type*}
    [CommRing A] [CommRing B] [CommRing L] [CommRing T]
    [Algebra A L] (M : Submonoid A) [IsLocalization M L]
    (i : A →+* L) (j : B →+* T)
    (hi : ∀ a, i a = algebraMap A L a)
    (E : L →+* T) (F : L →+* L) (G : T →+* T)
    (e : A → B) (f : A → A) (g : B → B)
    (hE : ∀ a, E (i a) = j (e a))
    (hF : ∀ a, F (i a) = i (f a))
    (hG : ∀ b, G (j b) = j (g b))
    (he : ∀ a, e (f a) = g (e a))
    (x : L) : E (F x) = G (E x) := by
  have h : E.comp F = G.comp E := by
    apply IsLocalization.ringHom_ext (M := M)
    apply RingHom.ext
    intro a
    change E (F (algebraMap A L a)) = G (E (algebraMap A L a))
    calc
      E (F (algebraMap A L a)) = E (F (i a)) :=
        congrArg (fun z => E (F z)) (hi a).symm
      _ = E (i (f a)) := congrArg E (hF a)
      _ = j (e (f a)) := hE (f a)
      _ = j (g (e a)) := congrArg j (he a)
      _ = G (j (e a)) := (hG (e a)).symm
      _ = G (E (i a)) := congrArg G (hE a).symm
      _ = G (E (algebraMap A L a)) := congrArg (fun z => G (E z)) (hi a)
  exact RingHom.congr_fun h x

theorem commutes_equiv
    {A B L T : Type*}
    [CommRing A] [CommRing B] [CommRing L] [CommRing T]
    [Algebra A L] (M : Submonoid A) [IsLocalization M L]
    (i : A →+* L) (j : B →+* T)
    (hi : ∀ a, i a = algebraMap A L a)
    (E : L ≃+* T) (F : L ≃+* L) (G : T ≃+* T)
    (e : A → B) (f : A → A) (g : B → B)
    (hE : ∀ a, E (i a) = j (e a))
    (hF : ∀ a, F (i a) = i (f a))
    (hG : ∀ b, G (j b) = j (g b))
    (he : ∀ a, e (f a) = g (e a))
    (x : L) : E (F x) = G (E x) :=
  commutes M i j hi E.toRingHom F.toRingHom G.toRingHom e f g hE hF hG he x

end JoshiTeich.Act1Scene1.LocalizationFrobeniusNaturality
