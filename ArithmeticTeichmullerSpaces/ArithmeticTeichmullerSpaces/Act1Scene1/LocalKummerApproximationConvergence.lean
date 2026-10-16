import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerFiniteApproximation
import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1CrossedTopology
import Mathlib.FieldTheory.Galois.Profinite

/-!
source-id: JT-SCENE1-KUMMER-CLASS-APPROXIMATION-CONVERGENCE
source: exact finite-level Kummer approximants, uniform Tate coordinate error
and the original compact-open cochains and H1 quotient topology.
fidelity: every integral cocycle's rational class is a limit of actual
field-element Kummer classes. The coefficient space, H1 and their topologies
are the original ones. No density or convergence certificate is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.Rational
open Filter Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [IsGalois K Ω] [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]

theorem exists_kummerClass_sequence_tendsto
    (f : continuousCocycles (K := K) (Ω := Ω) p) :
    ∃ a : ℕ → Kˣ, Tendsto (fun n => (kummerHom (Ω := Ω) p (a n)).toAdd)
      atTop (𝓝 (classOfCocycle p f)) := by
  choose a g hg hbound using exists_fieldKummer_coordinate_approximation p f
  let F : C((Ω ≃ₐ[K] Ω), ℚ_[p]) :=
    ⟨fun σ => coefficientMap p (Additive.ofMul (f.1 σ)),
      (continuous_coefficientMap p).comp (continuous_ofMul.comp f.1.continuous)⟩
  let A (n : ℕ) : C((Ω ≃ₐ[K] Ω), ℚ_[p]) :=
    ⟨fun σ => coefficientMap p (Additive.ofMul ((g n).1 σ)),
      (continuous_coefficientMap p).comp (continuous_ofMul.comp (g n).1.continuous)⟩
  have hA : Tendsto A atTop (𝓝 F) := by
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hpow := (tendsto_order.mp (tendsto_pow_atTop_nhds_zero_of_lt_one
      (norm_nonneg (p : ℚ_[p])) (Padic.norm_p_lt_one (p := p)))).2 ε hε
    filter_upwards [hpow] with n hn σ
    rw [dist_comm, dist_eq_norm]
    exact (hbound n σ).trans_lt hn
  let lift : C(ℚ_[p], topRep (K := K) (Ω := Ω) p) :=
    ⟨fun q => ULift.up q, continuous_uliftUp⟩
  have hC : Tendsto (fun n => cocycle p (g n)) atTop (𝓝 (cocycle p f)) :=
    (ContinuousMap.continuous_postcomp lift).continuousAt.tendsto.comp hA
  have hcross : Tendsto (fun n =>
      (⟨cocycle p (g n), cocycle_law p (g n)⟩ : ContinuousH1Homogeneous.Crossed (topRep p)))
      atTop (𝓝 ⟨cocycle p f, cocycle_law p f⟩) :=
    tendsto_subtype_rng.mpr hC
  have hclass := (ContinuousH1Homogeneous.continuous_crossed_class (topRep p)).continuousAt.tendsto.comp hcross
  refine ⟨a, ?_⟩
  change Tendsto (fun n => classOfCocycle p (g n)) atTop (𝓝 (classOfCocycle p f)) at hclass
  simpa only [hg] using hclass

end
end JoshiTeich.Act1Scene1.LocalKummer.Rational
