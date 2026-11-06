import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs

/-!
source-id: JT-SCENE1-FROBENIUS-MAP-IDENTITY-TRANSFER
source: Joshi II `se:ff-rings`, functorial Frobenius comparison under
change of a bounded localization presentation; composition of functions.
fidelity: transfers a proved commutation law through an original map
identity and an intertwining identity. The map identity is the first
explicit argument, so its original input and output types determine the
specialization. A second theorem obtains inverse intertwining directly
from a conjugation identity. Only functions and Equiv are used; no ring
instances, norm laws or comparison certificates are supplied.
Original proofs; no reference implementation copied.
boundary: generic function implications only; concrete consumers must
discharge every map identity and naturality law. Original-map and paper
identifications do not follow without those proofs.
-/

namespace JoshiTeich.Act1Scene1.FrobeniusMapIdentityTransfer

theorem commutes {A B C : Type*} {m : A → B} {t : C → B} {i : A → C}
    (hm : t ∘ i = m) {q : C → C} {G : B → B}
    (hnat : ∀ z, t (q z) = G (t z)) {F : A → A}
    (hiF : ∀ x, i (F x) = q (i x)) (x : A) :
    m (F x) = G (m x) := by
  calc
    m (F x) = t (i (F x)) := (congrFun hm (F x)).symm
    _ = t (q (i x)) := congrArg t (hiF x)
    _ = G (t (i x)) := hnat (i x)
    _ = G (m x) := congrArg G (congrFun hm x)

theorem inverse_intertwines {C A : Type*} {c : C ≃ A}
    {F : A → A} {q : C → C}
    (hq : q = c.symm ∘ F ∘ c) (x : A) :
    c.symm (F x) = q (c.symm x) := by
  calc
    c.symm (F x) = c.symm (F (c (c.symm x))) :=
      congrArg (fun y => c.symm (F y)) (c.apply_symm_apply x).symm
    _ = q (c.symm x) := (congrFun hq (c.symm x)).symm

end JoshiTeich.Act1Scene1.FrobeniusMapIdentityTransfer
