import Solutions.Source_ReferenceIutCor312CrystallineTopology
import Solutions.Source_ReferenceIutCor312CrystallineTatePadicScalars

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open Filter
open scoped Topology

noncomputable section

private theorem continuous_padicInt_ringHom_adic {R : Type*} [CommRing R]
    (p : ℕ) [Fact p.Prime] (f : PadicInt p →+* R) :
    let J : Ideal R := Ideal.span {(p : R)}
    Continuous[(inferInstance : TopologicalSpace (PadicInt p)), J.adicTopology] f := by
  let J : Ideal R := Ideal.span {(p : R)}
  letI : TopologicalSpace R := J.adicTopology
  letI : IsTopologicalRing R := J.nonarchimedean.toIsTopologicalRing
  change Continuous f
  apply continuous_of_tendsto_nhds_zero f
  refine J.hasBasis_nhds_zero_adic.tendsto_right_iff.mpr fun k _ => ?_
  let ε : ℝ := (p : ℝ) ^ (-(k : ℤ))
  have hp : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hball : Metric.closedBall (0 : PadicInt p) ε ∈ 𝓝 0 :=
    Metric.closedBall_mem_nhds _ (zpow_pos hp _)
  filter_upwards [hball] with x hx
  have hnorm : ‖x‖ ≤ ε := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hx' := (PadicInt.norm_le_pow_iff_mem_span_pow x k).mp hnorm
  change f x ∈ J ^ k
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  simpa only [map_pow, map_natCast] using map_dvd f (Ideal.mem_span_singleton.mp hx')

private theorem continuous_padic_ringHom_of_padicInt {R : Type*} [Ring R] [TopologicalSpace R]
    [IsTopologicalRing R] (p : ℕ) [Fact p.Prime] (f : Padic p →+* R)
    (hf : Continuous (fun x : PadicInt p => f (x : Padic p))) : Continuous f := by
  apply continuous_of_continuousAt_zero f
  have h0 : ContinuousAt (fun x : PadicInt p => f (x : Padic p)) (0 : PadicInt p) :=
    hf.continuousAt
  have h := PadicInt.isOpenEmbedding_coe.continuousAt_iff
    (g := (f : Padic p → R)) (x := (0 : PadicInt p))
  simpa only [PadicInt.coe_zero] using h.mp h0

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

/-- The integral $p$-adic scalar map is continuous for the adic topology. -/
theorem continuous_padicIntMapACris : Continuous (padicIntMapACris p C) :=
  continuous_padicInt_ringHom_adic p (padicIntMapACris p C)

/-- The rational $p$-adic scalar map into the first localization is continuous. -/
theorem continuous_padicMapACrisInvertP : Continuous (padicMapACrisInvertP p C) := by
  refine continuous_padic_ringHom_of_padicInt p (padicMapACrisInvertP p C) ?_
  have h : Continuous (padicIntMapACrisInvertP p C) :=
    (continuous_algebraMap_ACrisInvertP C p).comp (continuous_padicIntMapACris C p)
  have heq : (fun x : PadicInt p => padicMapACrisInvertP p C (x : Padic p)) =
      (padicIntMapACrisInvertP p C : PadicInt p → ACrisInvertP C p) :=
    funext fun x => by
      simpa only [PadicInt.algebraMap_apply] using padicMapACrisInvertP_algebraMap p C x
  rw [heq]
  exact h

variable {Ω : Type*} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (j : Ω →+* C)

/-- The same rational scalar map remains continuous after inverting the
original Tate period. -/
theorem continuous_padicMapACrisInvertTatePeriod :
    Continuous (padicMapACrisInvertTatePeriod C p j) :=
  (continuous_algebraMap_ACrisInvertTatePeriod C p j).comp (continuous_padicMapACrisInvertP C p)

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
