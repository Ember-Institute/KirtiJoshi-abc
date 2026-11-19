import Solutions.Source_ReferenceHeightsWeierstrassFibers
import Mathlib.Tactic.Ring

/-!
# Fibers of the first Weierstrass coordinate

The proof follows `Heights/WeierstrassFibers.lean` at
`721496ca4c158e511d25d8ccf6bfe8503eda73c1`. The cubic relation determines the derivative
up to sign, and the ordered-pair fiber theorem then identifies the lattice class.
-/

set_option autoImplicit false

open Set Filter Topology

noncomputable section

namespace AbcAdaptation.Reference.Heights

/-- The fibers of `℘` away from its poles are exactly the two classes related
by negation. -/
theorem weierstrassP_eq_iff_sub_mem_or_add_mem (L : PeriodPair) (z w : ℂ)
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
    L.weierstrassP z = L.weierstrassP w ↔
      z - w ∈ L.lattice ∨ z + w ∈ L.lattice := by
  constructor
  · intro hp
    have hzrel := L.derivWeierstrassP_sq z hz
    have hwrel := L.derivWeierstrassP_sq w hw
    have hp' : L.derivWeierstrassP z ^ 2 = L.derivWeierstrassP w ^ 2 := by
      rw [hzrel, hwrel, hp]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hp' with hp' | hp'
    · exact Or.inl <|
        sub_mem_lattice_of_weierstrassP_eq_of_deriv_eq L z w hz hw hp hp'
    · have hnwp : -w ∉ L.lattice := by simpa only [neg_mem_iff] using hw
      have hneg := sub_mem_lattice_of_weierstrassP_eq_of_deriv_eq L z (-w) hz hnwp
        (by simpa only [L.weierstrassP_neg] using hp)
        (by simpa only [L.derivWeierstrassP_neg] using hp')
      exact Or.inr (by simpa only [sub_neg_eq_add] using hneg)
  · rintro (hsub | hadd)
    · let l : L.lattice := ⟨z - w, hsub⟩
      have hzw : w + (l : ℂ) = z := by dsimp [l]; ring
      rw [← hzw, L.weierstrassP_add_coe]
    · let l : L.lattice := ⟨z + w, hadd⟩
      have hzw : -w + (l : ℂ) = z := by dsimp [l]; ring
      rw [← hzw, L.weierstrassP_add_coe, L.weierstrassP_neg]

end AbcAdaptation.Reference.Heights
