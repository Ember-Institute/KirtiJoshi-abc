import Mathlib.Algebra.Ring.Equiv

/-!
source-id: JT-SCENE1-RING-EQUIV-FROBENIUS-CONJUGATION-IDENTITY
source: Joshi II `se:ff-rings`, conjugation of Frobenius under a change
of bounded localization presentation; definitions of RingEquiv.trans.
fidelity: records full forward-function identities for composition and
conjugation of abstract ring equivalences. Only multiplication and addition
structures are required. The original equivalences and their functions
are retained; no ring, norm, algebra or comparison hypothesis is supplied.
Original proofs; no reference implementation copied.
boundary: generic definition identities only; concrete actual comparison,
Frobenius naturality, completion and paper identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.RingEquivFrobeniusConjugationIdentity

theorem conjugate_toFun {C A : Type*}
    [Mul C] [Add C] [Mul A] [Add A]
    (c : C ≃+* A) (F : A ≃+* A) :
    (c.trans (F.trans c.symm)).toEquiv.toFun =
      c.symm.toEquiv.toFun ∘ F.toEquiv.toFun ∘ c.toEquiv.toFun := rfl

theorem trans_toFun {C A B : Type*}
    [Mul C] [Add C] [Mul A] [Add A] [Mul B] [Add B]
    (c : C ≃+* A) (t : A ≃+* B) :
    (c.trans t).toEquiv.toFun = t.toEquiv.toFun ∘ c.toEquiv.toFun := rfl

end JoshiTeich.Act1Scene1.RingEquivFrobeniusConjugationIdentity
