/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/U2/CoreMap.lean
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationInertia

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

/-- The ramification index along a surjective ring map is `1`. -/
theorem ramificationIdx_of_surjective {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
    (hf : Function.Surjective f) (w : Ideal T) [w.IsPrime] :
    (letI := f.toAlgebra; w.ramificationIdx S) = 1 := by
  letI := f.toAlgebra
  haveI : Algebra.FormallyUnramified S T :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId S T) hf
  haveI : Algebra.FiniteType S T := Algebra.FiniteType.of_surjective (Algebra.ofId S T) hf
  have : Algebra.IsUnramifiedAt S w := Algebra.FormallyUnramified.comp S T _
  exact Ideal.ramificationIdx_eq_one w S

/-- Composing with an isomorphism on the right does not change ramification indices. -/
theorem ramificationIdx_comp_equiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDedekindDomain B] [IsDomain C] (g : A →+* B) (e : B ≃+* C) (w : Ideal C) [w.IsPrime] :
    (letI := ((e : B →+* C).comp g).toAlgebra; w.ramificationIdx A) =
      (letI := g.toAlgebra; (w.comap (e : B →+* C)).ramificationIdx A) := by
  rw [ramificationIdx_comp g (e : B →+* C) e.injective w,
    ramificationIdx_of_surjective (e : B →+* C) e.surjective w, mul_one]

/-- Composing with an isomorphism on the left does not change ramification indices. -/
theorem ramificationIdx_equiv_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDedekindDomain B] [IsDomain C] (e : A ≃+* B) (f : B →+* C) (hf : Function.Injective f)
    (w : Ideal C) [w.IsPrime] :
    (letI := (f.comp (e : A →+* B)).toAlgebra; w.ramificationIdx A) =
      (letI := f.toAlgebra; w.ramificationIdx B) := by
  have : (w.comap f).IsPrime := Ideal.IsPrime.comap f
  rw [ramificationIdx_comp (e : A →+* B) f hf w,
    ramificationIdx_of_surjective (e : A →+* B) e.surjective (w.comap f), one_mul]

/-- Ramification indices along equal ring maps agree. -/
theorem ramificationIdx_congr {R S : Type*} [CommRing R] [CommRing S] {f g : R →+* S} (h : f = g)
    (w : Ideal S) :
    (letI := f.toAlgebra; w.ramificationIdx R) = (letI := g.toAlgebra; w.ramificationIdx R) := by
  subst h; rfl

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
