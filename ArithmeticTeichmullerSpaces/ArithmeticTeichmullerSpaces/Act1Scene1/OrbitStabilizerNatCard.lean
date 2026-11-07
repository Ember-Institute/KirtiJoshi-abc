import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.NatCard

/-!
source-id: JT-SCENE1-GENERIC-ORBIT-STABILIZER-NAT-CARD-20261107
source: Mathlib's orbit-stabilizer equivalence for group actions.
fidelity: converts the orbit-product equivalence directly to `Nat.card`,
without requiring a chosen `Fintype` presentation.
boundary: generic group-action cardinality only; this file does not identify
any arithmetic fiber, ramification multiplicity, or paper representative.
-/

namespace JoshiTeich.Act1Scene1.OrbitStabilizerNatCard

variable {G X : Type*} [Group G] [MulAction G X]

theorem orbit_card_mul_stabilizer_card (x : X) :
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)

end JoshiTeich.Act1Scene1.OrbitStabilizerNatCard
