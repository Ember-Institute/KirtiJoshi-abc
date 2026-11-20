/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/M2/Final.lean
-/
import Solutions.Source_ReferenceIutCanLiftFrickePadicAction
import Solutions.Source_ReferenceIutCanLiftFrickeRationalCommensurator
import Solutions.Source_ReferenceIutCanLiftFrickeUnipotentCommensurator
import Solutions.Source_ReferenceIutCanLiftGoodLattice
import Solutions.Source_ReferenceIutCanLiftNonElementary
import Solutions.Source_ReferenceIutCanLiftPadicUnbounded
import Solutions.Source_ReferenceIutCanLiftSuperrigidity
import Solutions.Source_ReferenceIutCanLiftUnipotentPadic

set_option autoImplicit false

open MeasureTheory OnePoint OnePoint.Proj
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2

open Fricke (nA nB)

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)
  {X Y Z : ℚ} (hX : x ^ 2 = X) (hY : y ^ 2 = Y) (hZ : z ^ 2 = Z)

include hX hY hZ in
/-- **The `p`-adic step.** With `x², y², z² ∈ ℚ` and a dense commensurator, every squared trace
of the normal-form group is `p`-integral. -/
theorem padicNorm_trace_sq_le_one (hx : 0 < x) (hy : 0 < y) (h1 : x < y + z) (h2 : y < x + z)
    (h3 : z < x + y)
    (hdense : Dense (commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}) : Set SL(2, ℝ)))
    (p : ℕ) [Fact p.Prime] {γ : SL(2, ℝ)}
    (hγ : γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}) (hγ' : IsRatMul γ) :
    padicNorm p (hγ'.rep.trace ^ 2 / hγ'.rep.det) ≤ 1 := by
  classical
  letI : MeasurableSpace ℚ_[p] := borel _
  letI : BorelSpace ℚ_[p] := ⟨rfl⟩
  by_contra hbound
  have hlarge : 1 < padicNorm p (hγ'.rep.trace ^ 2 / hγ'.rep.det) := lt_of_not_ge hbound
  let Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  let Δ := commensurator Γ
  have hΓΔ : Γ ≤ Δ := le_commensurator Γ
  have hΔ : ∀ δ ∈ Δ, IsRatMul δ := fun δ hδ ↦ isRatMul_of_mem_commensurator hz hrel hX hY hZ hδ
  have hact : ActsOn Δ (aP p) := actsOn_aP p hΔ
  have hactΓ : ActsOn Γ (aP p) := hact.mono hΓΔ
  have hA : nA hz hrel ∈ Γ := Subgroup.subset_closure (by simp)
  have hK : commK hz hrel ∈ Γ := commK_mem hz hrel
  have hne : NonElem Γ (aP p) :=
    nonElem_of hactΓ hK hA (aP_commK p hz hrel (hΔ _ (hΓΔ hK)))
      (aP_nA_infty p hz hrel (hΔ _ (hΓΔ hA)) hx.ne')
  have hunb : Unbounded Γ (aP p) := by
    obtain ⟨τ, hτ, hlim⟩ :=
      Padic.exists_degenerate_limit (aP p γ) (aP_det_norm_lt_trace_norm_sq p hγ' hlarge)
    refine ⟨fun n ↦ γ ^ n, fun n ↦ pow_mem hγ n, τ, hτ, ?_⟩
    have hpow (n : ℕ) (w : OnePoint ℚ_[p]) : aP p (γ ^ n) • w = aP p γ ^ n • w :=
      (hactΓ.smul_pow hγ n w).trans (smul_iterate_apply (aP p γ) n w)
    simpa only [smul3, hpow] using hlim
  obtain ⟨Φ, hΦ, hext, hcont⟩ := commensurator_superrigidity (k := ℚ_[p])
    (goodLattice_normal hz hrel hx hy h1 h2 h3) hΓΔ le_rfl hdense hact hne hunb
  have hU2 : SL2R.uU 2 ∈ Δ := uU_two_mem_commensurator hz hrel
  have htr : UnipotentRigidity.IsTransl Φ 2 2 := fun w ↦
    (hext _ hU2 w).trans (aP_uU_two p (hΔ _ hU2) w)
  exact padic_contradiction hΦ hcont htr

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.M2
