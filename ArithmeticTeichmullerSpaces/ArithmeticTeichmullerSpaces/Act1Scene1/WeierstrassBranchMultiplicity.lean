import ArithmeticTeichmullerSpaces.Act1Scene1.WeierstrassBranchRamification
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's finite-flat ramification-inertia sum and the original coordinate basis.
fidelity: computes the actual x-projection's ramification index as two on its
two-torsion branch locus and one elsewhere. At a branch prime its residue
extension has degree one. No ramification or residue law is supplied as input.
boundary: Scene1/Derived. This concerns the ordinary affine double cover;
arbitrary AG.Orbicurve objects and the full producer remain open.
-/

namespace JoshiTeich.Act1Scene1.WeierstrassBranchLocus

open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k)

theorem ramificationIdx_mul_inertiaDeg_le_two
    (q : Ideal W.CoordinateRing) [q.IsPrime] :
    q.ramificationIdx k[X] * q.inertiaDeg k[X] ≤ 2 := by
  have : Module.Finite k[X] W.CoordinateRing :=
    Module.Finite.of_basis (Affine.CoordinateRing.basis W)
  let p := q.under k[X]
  let : Fintype (p.primesOver W.CoordinateRing) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  let r : p.primesOver W.CoordinateRing := Ideal.primesOver.mk p q
  calc
    q.ramificationIdx k[X] * q.inertiaDeg k[X] ≤
        ∑ s : p.primesOver W.CoordinateRing,
          s.1.ramificationIdx k[X] * s.1.inertiaDeg k[X] :=
      Finset.single_le_sum
        (f := fun s : p.primesOver W.CoordinateRing =>
          s.1.ramificationIdx k[X] * s.1.inertiaDeg k[X])
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    _ = 2 := by
      rw [Ideal.sum_ramification_inertia_eq_finrank,
        Module.finrank_eq_card_basis (Affine.CoordinateRing.basis W), Fintype.card_fin]

theorem ramificationIdx_pos (q : Ideal W.CoordinateRing) [q.IsPrime] :
    0 < q.ramificationIdx k[X] := by
  have : Module.Finite k[X] W.CoordinateRing :=
    Module.Finite.of_basis (Affine.CoordinateRing.basis W)
  exact q.ramificationIdx_pos k[X]

theorem ramificationIdx_le_two (q : Ideal W.CoordinateRing) [q.IsPrime] :
    q.ramificationIdx k[X] ≤ 2 := by
  have : Module.Finite k[X] W.CoordinateRing :=
    Module.Finite.of_basis (Affine.CoordinateRing.basis W)
  exact (Nat.le_mul_of_pos_right _ (q.inertiaDeg_pos k[X])).trans
    (ramificationIdx_mul_inertiaDeg_le_two W q)

variable [CharZero k]

theorem ramificationIdx_two_iff (q : Ideal W.CoordinateRing) [q.IsPrime] :
    q.ramificationIdx k[X] = 2 ↔ branchElement W ∈ q := by
  have hp := ramificationIdx_pos W q
  have hb := ramificationIdx_le_two W q
  have h := ramificationIdx_one_iff W q
  constructor
  · intro htwo
    by_contra hn
    have hone := h.mpr hn
    omega
  · intro hmem
    have hn : q.ramificationIdx k[X] ≠ 1 := fun he => (h.mp he) hmem
    omega

theorem ramificationIdx_two_iff_twoTorsion_mem
    (q : Ideal W.CoordinateRing) [q.IsPrime] :
    q.ramificationIdx k[X] = 2 ↔ W.twoTorsionPolynomial.toPoly ∈ q.under k[X] := by
  rw [ramificationIdx_two_iff, branchElement_mem_iff]

theorem inertiaDeg_one_of_branchElement_mem
    (q : Ideal W.CoordinateRing) [q.IsPrime] (hq : branchElement W ∈ q) :
    q.inertiaDeg k[X] = 1 := by
  have : Module.Finite k[X] W.CoordinateRing :=
    Module.Finite.of_basis (Affine.CoordinateRing.basis W)
  have hb := ramificationIdx_mul_inertiaDeg_le_two W q
  rw [(ramificationIdx_two_iff W q).mpr hq] at hb
  have hp := q.inertiaDeg_pos k[X]
  omega

theorem ramificationIdx_eq (q : Ideal W.CoordinateRing) [q.IsPrime] :
    q.ramificationIdx k[X] =
      if W.twoTorsionPolynomial.toPoly ∈ q.under k[X] then 2 else 1 := by
  split_ifs with h
  · exact (ramificationIdx_two_iff_twoTorsion_mem W q).mpr h
  · exact (ramificationIdx_one_iff_twoTorsion_not_mem W q).mpr h

end
end JoshiTeich.Act1Scene1.WeierstrassBranchLocus
