import ArithmeticTeichmullerSpaces.Act1Scene1.FrobeniusFunctionTransfer
import Mathlib.Logic.Equiv.Defs

/-!
source-id: JT-SCENE1-EQUIV-FROBENIUS-CONJUGATION
source: Joshi II `se:ff-rings`, functorial Frobenius comparison and change
of a bounded localization presentation; conjugation by an equivalence.
fidelity: transfers a proved function commutation law from a conjugated
source action to the comparison composed with the inverse equivalence.
The statements use only functions and Equiv. Naturality is the first
explicit argument. Optional function identities identify saved actions
and comparison maps without changing their carriers or functions.
Original proofs; no reference implementation copied.
boundary: generic function transport only; concrete consumers must prove
the original naturality and any supplied function identities. No operation
dictionary, norm, completion or paper identity is supplied.
-/

namespace JoshiTeich.Act1Scene1.EquivFrobeniusConjugation

theorem compose_symm {C A B : Type*} {c : C ≃ A}
    {t : C → B} {F : A → A} {G : B → B}
    (hnat : ∀ z, t (c.symm (F (c z))) = G (t z)) (x : A) :
    (t ∘ c.symm) (F x) = G ((t ∘ c.symm) x) := by
  change t (c.symm (F x)) = G (t (c.symm x))
  calc
    t (c.symm (F x)) = t (c.symm (F (c (c.symm x)))) :=
      congrArg (fun y => t (c.symm (F y))) (c.apply_symm_apply x).symm
    _ = G (t (c.symm x)) := hnat (c.symm x)

theorem compose_symm_function {C A B : Type*} {c : C ≃ A}
    {t : C → B} {F : A → A} {G : B → B}
    (hnat : ∀ z, t (c.symm (F (c z))) = G (t z)) :
    (t ∘ c.symm) ∘ F = G ∘ (t ∘ c.symm) := by
  funext x
  exact compose_symm hnat x

theorem transfer_conjugate {C A B : Type*}
    {t : C → B} {q : C → C} {G : B → B}
    (hnat : ∀ z, t (q z) = G (t z))
    (c : C ≃ A) (F : A → A)
    (hq : q = c.symm ∘ F ∘ c) (x : A) :
    (t ∘ c.symm) (F x) = G ((t ∘ c.symm) x) := by
  have hconj : ∀ z, t (c.symm (F (c z))) = G (t z) :=
    FrobeniusFunctionTransfer.transfer hnat hq.symm rfl
  exact compose_symm hconj x

theorem transfer_from_conjugate {C A B : Type*}
    {t : C → B} {q : C → C} {G : B → B}
    (hnat : ∀ z, t (q z) = G (t z))
    (c : C ≃ A) (F : A → A) (m : A → B)
    (hq : q = c.symm ∘ F ∘ c)
    (hm : t ∘ c.symm = m) (x : A) :
    m (F x) = G (m x) :=
  FrobeniusFunctionTransfer.transfer_map
    (transfer_conjugate hnat c F hq) hm x

theorem transfer_from_conjugate_pointwise {C A B : Type*}
    {t : C → B} {q : C → C} {G : B → B}
    (hnat : ∀ z, t (q z) = G (t z))
    (c : C ≃ A) (F : A → A) (m : A → B)
    (hq : ∀ z, q z = c.symm (F (c z)))
    (hm : ∀ x, m x = t (c.symm x)) (x : A) :
    m (F x) = G (m x) := by
  exact transfer_from_conjugate hnat c F m
    (funext hq) (funext (fun y => (hm y).symm)) x

end JoshiTeich.Act1Scene1.EquivFrobeniusConjugation
