import Mathlib.Topology.DenseEmbedding

/-!
source-id: JT-SCENE1-FROBENIUS-DENSE-TRANSPORT
source: Joshi II `se:ff-rings`, transport of a Frobenius square from a
dense bounded carrier to its completion.
fidelity: the helper has only explicit topological functions and a dense
inclusion. It introduces no comparison map, carrier, norm, Frobenius law,
or source assumption. Concrete users must provide the original functions,
continuity proofs, and bounded square. Original proof; no reference code copied.
boundary: generic density transport only; actual/standard carrier identities,
completion and paper B/period/BK obligations remain separate.
-/

namespace JoshiTeich.Act1Scene1.FrobeniusDenseTransport

open scoped Topology

theorem commute_of_dense
    {S A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [T2Space B]
    (i : S → A) (E : A → B) (F : A → A) (G : B → B)
    (hdense : DenseRange i)
    (hE : Continuous E) (hF : Continuous F) (hG : Continuous G)
    (hbounded : ∀ s, E (F (i s)) = G (E (i s)))
    (x : A) :
    E (F x) = G (E x) := by
  exact hdense.induction_on x
    (isClosed_eq (hE.comp hF) (hG.comp hE)) (fun s => hbounded s)

theorem commute_of_dense'
    {S A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [T2Space B]
    (i : S → A) (E : A → B) (F : A → A) (G : B → B)
    (hdense : DenseRange i)
    (hE : Continuous E) (hF : Continuous F) (hG : Continuous G)
    (hbounded : ∀ s, E (F (i s)) = G (E (i s))) :
    E ∘ F = G ∘ E := by
  funext x
  exact commute_of_dense i E F G hdense hE hF hG hbounded x

end JoshiTeich.Act1Scene1.FrobeniusDenseTransport
