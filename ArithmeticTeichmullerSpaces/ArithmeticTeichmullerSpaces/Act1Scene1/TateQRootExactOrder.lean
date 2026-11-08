import ArithmeticTeichmullerSpaces.Act1Scene1.IutTateTorsionResidue
import Mathlib.GroupTheory.OrderOfElement

/-!
source-id: IUT-COR312-TATE-TORSION-RESIDUE
source: the Tate quotient residue homomorphism from
`refer/iut/Iut/Anabelian/TateTorsion.lean`; Joshi III
`ss:theta-data-fixing2`, the paragraph "Existence of local torsion points
of order 2 ell" (TeX lines 1062--1064).
fidelity: if a unit u satisfies u^n=q, its point under the supplied Tate
quotient uniformization has exact additive order n. The existing residue
map sends this point to 1 in ZMod n, which proves the lower order bound.
The quotient uniformization and root equation remain explicit inputs.
boundary: Scene1/Derived; this is the general group argument. It does not
construct the arithmetic seed, choose a local root, or identify a paper
representative carrier. Original proof; no reference code copied.
-/

namespace JoshiTeich.Act1Scene1.IutTateQuotientUniformization

universe u v

noncomputable section

variable {K : Type u} [NormedField K] {A : Type v} [AddCommGroup A]
variable (S : IutTateQuotientUniformization K A)

/-- A root of the Tate parameter represents a point of exact order n. -/
theorem addOrderOf_ofUnit_eq_of_pow_eq_q
    {n : ℕ} {u : Kˣ} (hu : u ^ n = S.q) :
    addOrderOf (S.ofUnit u) = n := by
  have hP : S.ofUnit u ∈ iutTorsion A n :=
    (S.ofUnit_mem_torsionBy_iff n u).mpr ⟨1, by simpa only [zpow_one] using hu⟩
  let P : iutTorsion A n := ⟨S.ofUnit u, hP⟩
  have hResid : S.resid n P = (1 : ZMod n) := by
    simpa only [Int.cast_one] using
      S.resid_ofUnit n (n := (1 : ℤ)) (by simpa only [zpow_one] using hu) hP
  have hLower : n ∣ addOrderOf (S.ofUnit u) := by
    have hMap := addOrderOf_map_dvd (S.resid n) P
    rw [hResid, ZMod.addOrderOf_one] at hMap
    rw [← AddSubgroup.addOrderOf_coe P] at hMap
    exact hMap
  have hKill : n • S.ofUnit u = 0 :=
    (AddSubgroup.torsionBy.nsmul_iff).mp hP
  exact Nat.dvd_antisymm (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hKill) hLower

/-- In the nontrivial-order case, the root gives a nonzero point. -/
theorem ofUnit_ne_zero_of_pow_eq_q
    {n : ℕ} {u : Kˣ} (hu : u ^ n = S.q) (hn : 1 < n) :
    S.ofUnit u ≠ 0 := by
  intro hZero
  have hOrder := S.addOrderOf_ofUnit_eq_of_pow_eq_q hu
  rw [hZero, addOrderOf_zero] at hOrder
  exact (Nat.ne_of_gt hn) hOrder.symm

end

end JoshiTeich.Act1Scene1.IutTateQuotientUniformization
