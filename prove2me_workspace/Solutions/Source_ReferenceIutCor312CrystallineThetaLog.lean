import Solutions.Source_ReferenceIutCor312CrystallineThetaCompletion
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLog
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open Filter Topology JoshiTeich.Prologue
open scoped Valued

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [CharZero C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "𝒪" => (LocalGeometricFontaine.integerRing C)
local notation "θ" => (Perfectoid.thetaMap (O := 𝒪) (p := p))

private theorem dist_logPartialSum_thetaCrystalline_le (x : Ainf C p)
    (hx : x ∈ RingHom.ker θ ⊔ Ideal.span {(p : Ainf C p)})
    {k N : ℕ} (hN : p * k ≤ N) :
    dist (∑ n ∈ Finset.range N, LocalPadicLog.logTerm (1 + (θ x : C)) n)
      (thetaCrystalline C p (logOfMemKerSupPrime C p x hx) : C) ≤ ‖(p : C)‖ ^ k := by
  have hmem := Ideal.Quotient.eq.mp (eval_thetaCrystalline_logOfMemKerSupPrime C p x hx hN)
  rw [Ideal.span_singleton_pow] at hmem
  change _ ∈ (Ideal.span {((p : 𝒪) ^ k)} : Set 𝒪) at hmem
  rw [LocalGeometricFontaine.principalIdeal_eq_closedBall] at hmem
  rw [dist_comm, dist_eq_norm]
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, AddSubgroupClass.coe_sub,
    Subring.coe_pow, Subring.coe_natCast, norm_pow, thetaA0_logPartialSum,
    LocalPadicLog.logTerm, add_sub_cancel_left, Nat.cast_add, Nat.cast_one] using hmem

private theorem tendsto_logPartialSum_thetaCrystalline (x : Ainf C p)
    (hx : x ∈ RingHom.ker θ ⊔ Ideal.span {(p : Ainf C p)}) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, LocalPadicLog.logTerm (1 + (θ x : C)) n) atTop
      (𝓝 (thetaCrystalline C p (logOfMemKerSupPrime C p x hx) : C)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε
    (Fact.out : 0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1).2
  filter_upwards [eventually_ge_atTop (p * k)] with N hN
  exact (dist_logPartialSum_thetaCrystalline_le C p x hx hN).trans_lt hk

/-- The image of the crystalline logarithm is the sum of the ordinary logarithm series. -/
theorem hasSum_logTerm_thetaCrystalline (x : Ainf C p)
    (hx : x ∈ RingHom.ker θ ⊔ Ideal.span {(p : Ainf C p)}) :
    HasSum (LocalPadicLog.logTerm (1 + (θ x : C)))
      (thetaCrystalline C p (logOfMemKerSupPrime C p x hx) : C) := by
  have hs := tendsto_logPartialSum_thetaCrystalline C p x hx
  have hterms : Tendsto (LocalPadicLog.logTerm (1 + (θ x : C))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Finset.sum_range_succ, add_sub_cancel_left, sub_self] using
      (hs.comp (tendsto_add_atTop_nat 1)).sub hs
  exact (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (Nat.cofinite_eq_atTop ▸ hterms)).hasSum_iff_tendsto_nat.mpr hs

/-- When the principal unit comes from a discrete local field, the Fontaine image
is the image of its ordinary p-adic logarithm. -/
theorem thetaCrystalline_logOfMemKerSupPrime_eq_padicLog
    {k : Type*} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
    [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
    [CharZero k] [CompleteSpace k] (j : k →+* C) (hj : Continuous j)
    (hpk : ‖(p : k)‖ < 1) {u : k} (hu : ‖u - 1‖ < 1)
    (x : Ainf C p) (hx : x ∈ RingHom.ker θ ⊔ Ideal.span {(p : Ainf C p)})
    (hθ : j u = 1 + (θ x : C)) :
    (thetaCrystalline C p (logOfMemKerSupPrime C p x hx) : C) =
      j (LocalPadicLog.padicLog u) := by
  have h := (LocalPadicLog.hasSum_padicLog (Fact.out : p.Prime) hpk hu).map j hj
  have hterm : (⇑j ∘ LocalPadicLog.logTerm u) = LocalPadicLog.logTerm (j u) := by
    funext n
    simp only [Function.comp_apply, LocalPadicLog.logTerm, map_div₀, map_mul, map_pow, map_neg,
      map_one, map_sub, map_add, map_natCast]
  rw [hterm, hθ] at h
  exact (hasSum_logTerm_thetaCrystalline C p x hx).unique h

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
