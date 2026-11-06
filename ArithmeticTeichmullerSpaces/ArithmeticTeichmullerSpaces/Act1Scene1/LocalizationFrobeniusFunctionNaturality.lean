import Mathlib.RingTheory.Localization.Defs

/-!
source-id: JT-SCENE1-LOCALIZATION-FROBENIUS-FUNCTION-NATURALITY
source: Joshi II `se:ff-rings`, functorial Frobenius on bounded Witt
localizations; Mathlib IsLocalization.ext.
fidelity: proves commutation of three functions by checking the original
integral inclusion. Each function has explicit unit and multiplication
laws. The proof applies localization extensionality directly to the
composed functions. A concrete consumer must prove all source laws from
its existing maps. Original proof; no reference implementation copied.
boundary: this generic implication supplies no actual comparison law,
norm law, completion identity, or paper B identity.
-/

namespace JoshiTeich.Act1Scene1.LocalizationFrobeniusFunctionNaturality

theorem commutes
    {A B L T : Type*}
    [CommRing A] [CommRing B] [CommRing L] [CommRing T]
    [Algebra A L] (M : Submonoid A) [IsLocalization M L]
    (i : A → L) (j : B → T)
    (hi : ∀ a, i a = algebraMap A L a)
    (E : L → T) (F : L → L) (G : T → T)
    (hE_one : E 1 = 1) (hF_one : F 1 = 1) (hG_one : G 1 = 1)
    (hE_mul : ∀ a b, E (a * b) = E a * E b)
    (hF_mul : ∀ a b, F (a * b) = F a * F b)
    (hG_mul : ∀ a b, G (a * b) = G a * G b)
    (e : A → B) (f : A → A) (g : B → B)
    (hE : ∀ a, E (i a) = j (e a))
    (hF : ∀ a, F (i a) = i (f a))
    (hG : ∀ b, G (j b) = j (g b))
    (he : ∀ a, e (f a) = g (e a))
    (x : L) : E (F x) = G (E x) := by
  have h : (fun z : L => E (F z)) = (fun z : L => G (E z)) := by
    apply IsLocalization.ext (M := M)
    · exact (congrArg E hF_one).trans hE_one
    · exact (congrArg G hE_one).trans hG_one
    · intro a b
      exact (congrArg E (hF_mul a b)).trans (hE_mul (F a) (F b))
    · intro a b
      exact (congrArg G (hE_mul a b)).trans (hG_mul (E a) (E b))
    · intro a
      calc
        E (F (algebraMap A L a)) = E (F (i a)) :=
          congrArg (fun z => E (F z)) (hi a).symm
        _ = E (i (f a)) := congrArg E (hF a)
        _ = j (e (f a)) := hE (f a)
        _ = j (g (e a)) := congrArg j (he a)
        _ = G (j (e a)) := (hG (e a)).symm
        _ = G (E (i a)) := congrArg G (hE a).symm
        _ = G (E (algebraMap A L a)) :=
          congrArg (fun z => G (E z)) (hi a)
  exact congrFun h x

end JoshiTeich.Act1Scene1.LocalizationFrobeniusFunctionNaturality
