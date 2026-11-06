import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Algebra.Ring.Equiv

/-!
source-id: JT-SCENE1-FIXED-SUBRING-DESCENT-20261107
source: IUT I Definition 3.1(d), signed quotient of the covering curve;
the universal property of an explicitly identified invariant subring.
fidelity: maps with image in a given subsemiring factor uniquely through
any ring that is isomorphic to that subsemiring by the original inclusion.
Original proofs; no reference implementation copied.
boundary: ordinary coordinate-ring descent, without a stack realization.
-/

namespace JoshiTeich.Act1Scene1

noncomputable section

theorem fixedSubring_factor_unique
    {A B C : Type*} [Semiring A] [Semiring B] [Semiring C]
    (s : Subsemiring B) (e : A ≃+* s) (i : A →+* B)
    (hi : ∀ a, (e a : B) = i a) (f : C →+* B) (hf : ∀ c, f c ∈ s) :
    ∃! q : C →+* A, i.comp q = f := by
  let q : C →+* A := e.symm.toRingHom.comp (f.codRestrict s hf)
  have hq : i.comp q = f := by
    apply RingHom.ext
    intro c
    exact (hi (q c)).symm.trans
      (congrArg (fun x : s => (x : B)) (e.apply_symm_apply ⟨f c, hf c⟩))
  have hinj : Function.Injective i := by
    intro a b hab
    apply e.injective
    apply Subtype.ext
    exact (hi a).trans (hab.trans (hi b).symm)
  refine ⟨q, hq, ?_⟩
  intro r hr
  exact RingHom.ext fun c => hinj
    ((RingHom.congr_fun hr c).trans (RingHom.congr_fun hq c).symm)

end
end JoshiTeich.Act1Scene1
