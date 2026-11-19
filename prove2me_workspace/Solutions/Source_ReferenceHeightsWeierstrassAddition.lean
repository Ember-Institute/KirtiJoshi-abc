import Solutions.Source_ReferenceHeightsWeierstrassAdditionLocal
import Solutions.Source_ReferenceHeightsWeierstrassPFiber

/-!
# Global addition formulas for the Weierstrass coordinates

The global continuation argument follows `Heights/WeierstrassAddition.lean` at
`721496ca4c158e511d25d8ccf6bfe8503eda73c1`. The secant formulas extend from a
neighborhood of zero to the complement of the countable exceptional set.
-/

set_option autoImplicit false

open Set Filter Topology

noncomputable section

namespace AbcAdaptation.Reference.Heights

/-- The global Weierstrass secant addition formula away from its genuine
exceptional points.  The hypotheses exclude poles of the two inputs and their
sum, and exclude a vertical secant. -/
theorem weierstrass_addition_coordinates (L : PeriodPair) (z w : ℂ)
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (hzw : z + w ∉ L.lattice)
    (hne : L.weierstrassP z ≠ L.weierstrassP w) :
    weierstrassSecantAddX L (L.weierstrassP w) (L.derivWeierstrassP w) z =
        L.weierstrassP (z + w) ∧
      weierstrassSecantAddY L (L.weierstrassP w) (L.derivWeierstrassP w) z =
        L.derivWeierstrassP (z + w) / 2 := by
  let A : Set ℂ := (L.lattice : Set ℂ) \ {0}
  let Bm : Set ℂ := (fun u : ℂ ↦ u - w) ⁻¹' (L.lattice : Set ℂ)
  let Bp : Set ℂ := (fun u : ℂ ↦ u + w) ⁻¹' (L.lattice : Set ℂ)
  let C : Set ℂ := (fun u : ℂ ↦ u + w) ⁻¹' (L.lattice : Set ℂ)
  let D : Set ℂ := ((A ∪ Bm) ∪ Bp) ∪ C
  let U : Set ℂ := Dᶜ
  have hlattice : (L.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L.lattice)
  have hA : A.Countable := hlattice.mono sdiff_le
  have hBm : Bm.Countable := hlattice.preimage sub_left_injective
  have hBp : Bp.Countable := hlattice.preimage fun _ _ h ↦ add_right_cancel h
  have hC : C.Countable := hlattice.preimage fun _ _ h ↦ add_right_cancel h
  have hD : D.Countable := ((hA.union hBm).union hBp).union hC
  have hUpre : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) hD).2
  have h0U : (0 : ℂ) ∈ U := by
    simp [U, D, A, Bm, Bp, C, hw]
  have hzU : z ∈ U := by
    have hzA : z ∉ A := fun h ↦ hz h.1
    have hzBm : z ∉ Bm := by
      intro h
      exact hne <| (weierstrassP_eq_iff_sub_mem_or_add_mem L z w hz hw).2
        (Or.inl h)
    have hzBp : z ∉ Bp := by
      intro h
      exact hne <| (weierstrassP_eq_iff_sub_mem_or_add_mem L z w hz hw).2
        (Or.inr h)
    have hzC : z ∉ C := by
      simpa [C, add_comm] using hzw
    simpa only [U, D, mem_compl_iff, mem_union, not_or] using
      ⟨⟨⟨hzA, hzBm⟩, hzBp⟩, hzC⟩
  have hX : AnalyticOnNhd ℂ
      (weierstrassSecantAddXAtZero L (L.weierstrassP w)
        (L.derivWeierstrassP w)) U := by
    intro u hu
    by_cases hu0 : u = 0
    · simpa [hu0] using analyticAt_weierstrassSecantAddXAtZero L
        (L.weierstrassP w) (L.derivWeierstrassP w)
        (L.derivWeierstrassP_sq w hw)
    · have huD : u ∉ D := by simpa [U] using hu
      have huA : u ∉ A := by
        intro h
        exact huD (Or.inl (Or.inl (Or.inl h)))
      have hul : u ∉ L.lattice := by
        intro h
        exact huA ⟨h, by simpa using hu0⟩
      have huBm : u ∉ Bm := by
        intro h
        exact huD (Or.inl (Or.inl (Or.inr h)))
      have huBp : u ∉ Bp := by
        intro h
        exact huD (Or.inl (Or.inr h))
      have hpne : L.weierstrassP u ≠ L.weierstrassP w := by
        intro hp
        rcases (weierstrassP_eq_iff_sub_mem_or_add_mem L u w hul hw).1 hp with
          hm | hp
        · exact huBm hm
        · exact huBp hp
      have hp : AnalyticAt ℂ L.weierstrassP u :=
        L.analyticOnNhd_weierstrassP u hul
      have hdp : AnalyticAt ℂ L.derivWeierstrassP u :=
        L.analyticOnNhd_derivWeierstrassP u hul
      have hm : AnalyticAt ℂ
          (weierstrassSecantSlope L (L.weierstrassP w)
            (L.derivWeierstrassP w)) u := by
        unfold weierstrassSecantSlope
        exact (hdp.sub analyticAt_const).div
          (analyticAt_const.mul (hp.sub analyticAt_const))
          (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hpne))
      have horig : AnalyticAt ℂ
          (weierstrassSecantAddX L (L.weierstrassP w)
            (L.derivWeierstrassP w)) u := by
        unfold weierstrassSecantAddX
        exact ((hm.pow 2).sub hp).sub analyticAt_const
      apply horig.congr
      filter_upwards [isOpen_ne.mem_nhds hu0] with v hv
      simp [weierstrassSecantAddXAtZero, hv]
  have hY : AnalyticOnNhd ℂ
      (weierstrassSecantAddYAtZero L (L.weierstrassP w)
        (L.derivWeierstrassP w)) U := by
    intro u hu
    by_cases hu0 : u = 0
    · simpa [hu0] using analyticAt_weierstrassSecantAddYAtZero L
        (L.weierstrassP w) (L.derivWeierstrassP w)
        (L.derivWeierstrassP_sq w hw)
    · have huD : u ∉ D := by simpa [U] using hu
      have huA : u ∉ A := by
        intro h
        exact huD (Or.inl (Or.inl (Or.inl h)))
      have hul : u ∉ L.lattice := by
        intro h
        exact huA ⟨h, by simpa using hu0⟩
      have huBm : u ∉ Bm := by
        intro h
        exact huD (Or.inl (Or.inl (Or.inr h)))
      have huBp : u ∉ Bp := by
        intro h
        exact huD (Or.inl (Or.inr h))
      have hpne : L.weierstrassP u ≠ L.weierstrassP w := by
        intro hp
        rcases (weierstrassP_eq_iff_sub_mem_or_add_mem L u w hul hw).1 hp with
          hm | hp
        · exact huBm hm
        · exact huBp hp
      have hp : AnalyticAt ℂ L.weierstrassP u :=
        L.analyticOnNhd_weierstrassP u hul
      have hdp : AnalyticAt ℂ L.derivWeierstrassP u :=
        L.analyticOnNhd_derivWeierstrassP u hul
      have hm : AnalyticAt ℂ
          (weierstrassSecantSlope L (L.weierstrassP w)
            (L.derivWeierstrassP w)) u := by
        unfold weierstrassSecantSlope
        exact (hdp.sub analyticAt_const).div
          (analyticAt_const.mul (hp.sub analyticAt_const))
          (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hpne))
      have hxorig : AnalyticAt ℂ
          (weierstrassSecantAddX L (L.weierstrassP w)
            (L.derivWeierstrassP w)) u := by
        unfold weierstrassSecantAddX
        exact ((hm.pow 2).sub hp).sub analyticAt_const
      have horig : AnalyticAt ℂ
          (weierstrassSecantAddY L (L.weierstrassP w)
            (L.derivWeierstrassP w)) u := by
        unfold weierstrassSecantAddY
        have hhalf : AnalyticAt ℂ (fun v ↦ L.derivWeierstrassP v / 2) u :=
          hdp.div_const
        exact (hm.mul (hp.sub hxorig)).sub hhalf
      apply horig.congr
      filter_upwards [isOpen_ne.mem_nhds hu0] with v hv
      simp [weierstrassSecantAddYAtZero, hv]
  have hTX : AnalyticOnNhd ℂ (fun u ↦ L.weierstrassP (u + w)) U := by
    intro u hu
    have huD : u ∉ D := by simpa [U] using hu
    have huC : u ∉ C := by
      intro h
      exact huD (Or.inr h)
    change AnalyticAt ℂ (L.weierstrassP ∘ fun v : ℂ ↦ v + w) u
    have hi : AnalyticAt ℂ (fun v : ℂ ↦ v + w) u :=
      analyticAt_id.add analyticAt_const
    exact (L.analyticOnNhd_weierstrassP (u + w) huC).comp
      (f := fun v : ℂ ↦ v + w) hi
  have hTY : AnalyticOnNhd ℂ
      (fun u ↦ L.derivWeierstrassP (u + w) / 2) U := by
    intro u hu
    have huD : u ∉ D := by simpa [U] using hu
    have huC : u ∉ C := by
      intro h
      exact huD (Or.inr h)
    have hd : AnalyticAt ℂ (fun v ↦ L.derivWeierstrassP (v + w)) u := by
      change AnalyticAt ℂ (L.derivWeierstrassP ∘ fun v : ℂ ↦ v + w) u
      have hi : AnalyticAt ℂ (fun v : ℂ ↦ v + w) u :=
        analyticAt_id.add analyticAt_const
      exact (L.analyticOnNhd_derivWeierstrassP (u + w) huC).comp
        (f := fun v : ℂ ↦ v + w) hi
    fun_prop
  have hlocalX := weierstrassSecantAddXAtZero_eventuallyEq_translate L w hw
  have hlocalX' : weierstrassSecantAddXAtZero L (L.weierstrassP w)
      (L.derivWeierstrassP w) =ᶠ[𝓝 0]
      (fun u ↦ L.weierstrassP (u + w)) := by
    filter_upwards [hlocalX] with u hu
    simpa [add_comm] using hu
  have hlocalY := weierstrassSecantAddYAtZero_eventuallyEq_translate L w hw
  have hlocalY' : weierstrassSecantAddYAtZero L (L.weierstrassP w)
      (L.derivWeierstrassP w) =ᶠ[𝓝 0]
      (fun u ↦ L.derivWeierstrassP (u + w) / 2) := by
    filter_upwards [hlocalY] with u hu
    simpa [add_comm] using hu
  have hglobalX := hX.eqOn_of_preconnected_of_eventuallyEq hTX hUpre h0U hlocalX'
  have hglobalY := hY.eqOn_of_preconnected_of_eventuallyEq hTY hUpre h0U hlocalY'
  have hx0 : z ≠ 0 := by
    intro h
    subst z
    exact hz L.lattice.zero_mem
  constructor
  · simpa [weierstrassSecantAddXAtZero, hx0] using hglobalX hzU
  · simpa [weierstrassSecantAddYAtZero, hx0] using hglobalY hzU

end AbcAdaptation.Reference.Heights
