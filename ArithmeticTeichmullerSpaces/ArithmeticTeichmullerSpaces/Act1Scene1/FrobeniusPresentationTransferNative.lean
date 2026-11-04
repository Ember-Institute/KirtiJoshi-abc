import ArithmeticTeichmullerSpaces.Act1Scene1.FrobeniusPresentationTransfer

/-!
source-id: JT-SCENE1-FROBENIUS-PRESENTATION-TRANSFER-NATIVE
source: Joshi II `se:ff-rings`, functorial Frobenius comparison through
the original bounded Witt presentations.
fidelity: applies the proved pure presentation transfer theorem with the
source coverage and target uniqueness laws as its first explicit inputs.
These inputs fix the two presentation relations before the comparison
and action laws are supplied. All relations, functions and premises are
unchanged. No ring instances, bundled maps, or additional certificates
are introduced. Original proof; no reference implementation copied.
boundary: generic presentation implication only; concrete consumers must
discharge every law from their original maps. No completion, paper B,
period or BK identity is supplied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.FrobeniusPresentationTransferNative

theorem commutes {A B L T : Type*}
    {P : L → ℕ → A → Prop} {Q : T → ℕ → B → Prop}
    {E : L → T} {F : L → L} {G : T → T} {f : A → B}
    {index : ℕ → ℕ} {tA : ℕ → A → A} {tB : ℕ → B → B}
    (covers : ∀ x, ∃ m a, P x m a)
    (unique : ∀ y z m b, Q y m b → Q z m b → y = z)
    (hE : ∀ x m a, P x m a → Q (E x) m (f a))
    (hF : ∀ x m a, P x m a → P (F x) (index m) (tA m a))
    (hG : ∀ y m b, Q y m b → Q (G y) (index m) (tB m b))
    (he : ∀ m a, f (tA m a) = tB m (f a))
    (x : L) : E (F x) = G (E x) :=
  FrobeniusPresentationTransfer.commutes hE covers unique hF hG he x

end JoshiTeich.Act1Scene1.FrobeniusPresentationTransferNative
