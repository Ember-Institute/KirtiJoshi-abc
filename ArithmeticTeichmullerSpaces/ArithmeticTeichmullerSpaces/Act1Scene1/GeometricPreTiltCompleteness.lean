import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltSharp
import Mathlib.Topology.MetricSpace.Cauchy

/-!
source-id: JT-SCENE1-GEOMETRIC-PRETILT-COMPLETENESS
source: Joshi tilt after lem:perfectoid; Mathlib PreTilt inverse limit,
coefficient valuation and canonical untilting. Original proofs.
fidelity: equips the same actual PreTilt with its valuation norm and proves
completeness by eventual stabilization of every coefficient of a Cauchy
sequence. No completion replaces the carrier. Completeness of its fraction
field and the selected paper tilt identification remain separate obligations.
boundary: Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.GeometricPreTiltCompleteness

open JoshiTeich.Prologue Filter
open scoped NNReal Topology
universe u
noncomputable section
variable (Ω : Type u) [NormedField Ω] [IsUltrametricDist Ω] [CompleteSpace Ω]
variable (p : ℕ) [Fact p.Prime]
variable [hp : Fact (0 < ‖(p : Ω)‖ ∧ ‖(p : Ω)‖ < 1)]

/-- The norm is the actual PreTilt valuation, without any rescaling. -/
def absoluteValue : AbsoluteValue (GeometricTiltField.Source Ω p) ℝ where
  toFun x := GeometricTiltField.sourceValuation Ω p x
  map_mul' x y := by exact_mod_cast map_mul (GeometricTiltField.sourceValuation Ω p) x y
  nonneg' x := (GeometricTiltField.sourceValuation Ω p x).property
  eq_zero' x := by
    rw [NNReal.coe_eq_zero]
    exact GeometricTiltField.sourceValuation_eq_zero_iff Ω p x
  add_le' x y := by
    exact (NNReal.coe_le_coe.mpr ((GeometricTiltField.sourceValuation Ω p).map_add x y)).trans
      (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

instance sourceNormedRing : NormedRing (GeometricTiltField.Source Ω p) :=
  (absoluteValue Ω p).toNormedRing

omit [CompleteSpace Ω] in
theorem norm_eq_valuation (x : GeometricTiltField.Source Ω p) :
    ‖x‖ = (GeometricTiltField.sourceValuation Ω p x : ℝ) := rfl

/-- Exact closed-ball criterion for the n-th coefficient to vanish. -/
theorem coeff_eq_zero_iff (x : GeometricTiltField.Source Ω p) (n : ℕ) :
    PreTilt.coeff n x = 0 ↔ ‖x‖ ≤ ‖(p : Ω)‖ ^ p ^ n := by
  let y := ((frobeniusEquiv (GeometricTiltField.Source Ω p) p).symm^[n]) x
  have hc : PreTilt.coeff 0 y = PreTilt.coeff n x := by
    simpa only [Nat.zero_add] using PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n x
  have hr := (PreTilt.mk_untilt_eq_coeff_zero y).trans hc
  have hz : PreTilt.coeff n x = 0 ↔
      ‖((PreTilt.untilt y : LocalGeometricFontaine.integerRing Ω) : Ω)‖ ≤ ‖(p : Ω)‖ := by
    rw [← hr, Ideal.Quotient.eq_zero_iff_mem]
    change PreTilt.untilt y ∈ (Ideal.span {(p : LocalGeometricFontaine.integerRing Ω)} :
      Set (LocalGeometricFontaine.integerRing Ω)) ↔ _
    rw [LocalGeometricFontaine.principalIdeal_eq_closedBall]
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, Subring.coe_natCast]
  have hpow : ((PreTilt.untilt y : LocalGeometricFontaine.integerRing Ω) : Ω) ^ p ^ n =
      ((PreTilt.untilt x : LocalGeometricFontaine.integerRing Ω) : Ω) := by
    have h := congrArg (fun z : LocalGeometricFontaine.integerRing Ω => (z : Ω))
      (PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n)
    simpa only [Subring.coe_pow] using h
  have hn : ‖x‖ = ‖((PreTilt.untilt y : LocalGeometricFontaine.integerRing Ω) : Ω)‖ ^ p ^ n := by
    rw [norm_eq_valuation, GeometricTiltSharp.sourceValuation_eq_sharp_norm]
    change ‖GeometricTiltSharp.integralSharp Ω p x‖ = _
    rw [GeometricTiltSharp.integralSharp_eq_untilt]
    change ‖((PreTilt.untilt x : LocalGeometricFontaine.integerRing Ω) : Ω)‖ = _
    rw [← hpow, norm_pow]
  rw [hz, hn]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).symm

theorem coeff_eq_iff_dist_le (x y : GeometricTiltField.Source Ω p) (n : ℕ) :
    PreTilt.coeff n x = PreTilt.coeff n y ↔ dist x y ≤ ‖(p : Ω)‖ ^ p ^ n := by
  rw [← sub_eq_zero, ← map_sub, coeff_eq_zero_iff, dist_eq_norm]

omit [IsUltrametricDist Ω] [CompleteSpace Ω] in
/-- These exact coefficient balls shrink to zero. -/
theorem exists_coeffRadius_lt (ε : ℝ) (hε : 0 < ε) : ∃ n : ℕ, ‖(p : Ω)‖ ^ p ^ n < ε := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hp.out.2
  refine ⟨m, lt_of_le_of_lt ?_ hm⟩
  apply pow_le_pow_of_le_one (norm_nonneg _) hp.out.2.le
  exact (Nat.le_of_lt (show m < 2 ^ m from Nat.lt_two_pow_self)).trans
    (Nat.pow_le_pow_left (Fact.out : p.Prime).two_le m)

/-- Every coefficient of a valuation-Cauchy sequence is eventually constant. -/
theorem cauchySeq_coeff_stable (s : ℕ → GeometricTiltField.Source Ω p) (hs : CauchySeq s) (n : ℕ) :
    ∃ N, ∀ m ≥ N, PreTilt.coeff n (s m) = PreTilt.coeff n (s N) := by
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hs (‖(p : Ω)‖ ^ p ^ n) (pow_pos hp.out.1 _)
  exact ⟨N, fun m hm => (coeff_eq_iff_dist_le Ω p (s m) (s N) n).mpr (hN m hm).le⟩

/-- The inverse-limit limit is made of the stabilized actual coefficients. -/
def cauchyLimit (s : ℕ → GeometricTiltField.Source Ω p) (hs : CauchySeq s) :
    GeometricTiltField.Source Ω p := by
  let N := fun n => Classical.choose (cauchySeq_coeff_stable Ω p s hs n)
  have hN : ∀ n m, N n ≤ m → PreTilt.coeff n (s m) = PreTilt.coeff n (s (N n)) :=
    fun n => Classical.choose_spec (cauchySeq_coeff_stable Ω p s hs n)
  refine ⟨fun n => PreTilt.coeff n (s (N n)), ?_⟩
  intro n
  change PreTilt.coeff (n + 1) (s (N (n + 1))) ^ p = PreTilt.coeff n (s (N n))
  let m := max (N (n + 1)) (N n)
  rw [← hN (n + 1) m (le_max_left _ _), ← hN n m (le_max_right _ _)]
  exact PreTilt.coeff_pow_p (s m) n

theorem coeff_cauchyLimit_eventually (s : ℕ → GeometricTiltField.Source Ω p) (hs : CauchySeq s)
    (n : ℕ) : ∀ᶠ m in atTop, PreTilt.coeff n (s m) = PreTilt.coeff n (cauchyLimit Ω p s hs) := by
  let N := Classical.choose (cauchySeq_coeff_stable Ω p s hs n)
  refine eventually_atTop.mpr ⟨N, ?_⟩
  intro m hm
  change PreTilt.coeff n (s m) = PreTilt.coeff n (s N)
  exact Classical.choose_spec (cauchySeq_coeff_stable Ω p s hs n) m hm

theorem cauchyLimit_tendsto (s : ℕ → GeometricTiltField.Source Ω p) (hs : CauchySeq s) :
    Tendsto s atTop (𝓝 (cauchyLimit Ω p s hs)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := exists_coeffRadius_lt Ω p ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (coeff_cauchyLimit_eventually Ω p s hs n)
  exact ⟨N, fun m hm => ((coeff_eq_iff_dist_le Ω p (s m) (cauchyLimit Ω p s hs) n).mp
    (hN m hm)).trans_lt hn⟩

instance sourceCompleteSpace : CompleteSpace (GeometricTiltField.Source Ω p) :=
  Metric.complete_of_cauchySeq_tendsto fun s hs => ⟨cauchyLimit Ω p s hs, cauchyLimit_tendsto Ω p s hs⟩

end
end JoshiTeich.Act1Scene1.GeometricPreTiltCompleteness
