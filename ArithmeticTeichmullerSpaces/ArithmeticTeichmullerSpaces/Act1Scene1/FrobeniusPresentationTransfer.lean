import Mathlib.Logic.Function.Defs

/-!
source-id: JT-SCENE1-FROBENIUS-PRESENTATION-TRANSFER
source: Joshi II `se:ff-rings`, functorial Frobenius comparison through
presentations of bounded Witt elements.
fidelity: proves commutation of functions from covering source
presentations and uniqueness of target presentations. The comparison and
the two actions preserve the given presentation relations, and the
integral comparison intertwines the presented numerators. All functions
and relations are supplied directly; no ring instances or bundled maps
occur. Concrete consumers must discharge each presentation law from
their original constructions. Original proof; no reference implementation
copied.
boundary: generic presentation implication only; no concrete presentation
law, norm law, completion or paper B, period or BK identity is supplied.
Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.FrobeniusPresentationTransfer

theorem commutes {A B L T : Type*}
    {P : L → ℕ → A → Prop} {Q : T → ℕ → B → Prop}
    {E : L → T} {F : L → L} {G : T → T} {f : A → B}
    {index : ℕ → ℕ} {tA : ℕ → A → A} {tB : ℕ → B → B}
    (hE : ∀ x m a, P x m a → Q (E x) m (f a))
    (covers : ∀ x, ∃ m a, P x m a)
    (unique : ∀ y z m b, Q y m b → Q z m b → y = z)
    (hF : ∀ x m a, P x m a → P (F x) (index m) (tA m a))
    (hG : ∀ y m b, Q y m b → Q (G y) (index m) (tB m b))
    (he : ∀ m a, f (tA m a) = tB m (f a))
    (x : L) : E (F x) = G (E x) := by
  obtain ⟨m, a, hx⟩ := covers x
  apply unique (E (F x)) (G (E x)) (index m) (f (tA m a))
  · exact hE (F x) (index m) (tA m a) (hF x m a hx)
  · rw [he m a]
    exact hG (E x) m (f a) (hE x m a hx)

end JoshiTeich.Act1Scene1.FrobeniusPresentationTransfer
