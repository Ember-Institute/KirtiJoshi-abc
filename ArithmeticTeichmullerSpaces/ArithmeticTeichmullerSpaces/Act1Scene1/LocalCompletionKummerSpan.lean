import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerApproximationConvergence
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionKummerValuationSplit
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerH1Denominator
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerSaturatedTopology

/-!
source-id: JT-SCENE1-COMPLETION-KUMMER-SPAN
source: actual completion finite dimension, unit/prime Kummer decomposition,
finite-level approximation and original H1 denominator clearing.
fidelity: proves that actual field-element Kummer classes span all rational
continuous H1. The finite-dimensional Kummer span is closed, and contains
the limits supplied by finite-level approximation. Thus the earlier unit
and prime-line decomposition now covers ambient H1. No H1e/BK identity.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.KummerValuation
open NumberField JoshiTeich.Prologue Filter Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] [NumberField K] (w : FinitePlace K)
variable (p : ℕ) [Fact p.Prime] (hpw : Arithmetic.residueChar w = p)
variable {Ω : Type v} [Field Ω] [Algebra (completionAt K w) Ω]
variable [IsGalois (completionAt K w) Ω] [Algebra.IsIntegral (completionAt K w) Ω]
variable [CharZero Ω] [IsAlgClosed Ω]
local instance spanCharZero : CharZero (completionAt K w) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective
local notation "H" => continuousCohomology 1 (LocalKummer.Rational.topRep
  (K := completionAt K w) (Ω := Ω) p)
include hpw

theorem multiplicativeSpan_finiteDimensional : FiniteDimensional ℚ_[p] (multiplicativeSpan w p (Ω := Ω)) := by
  letI := padicAlgebra hpw
  letI : Module.Finite ℚ_[p] (completionAt K w) := finite_padicAlgebra hpw
  letI : ContinuousSMul ℚ_[p] (completionAt K w) :=
    continuousSMul_of_algebraMap _ _ (continuous_padicEmb hpw)
  haveI : FiniteDimensional ℚ_[p] (unitsSubspace w p hpw (Ω := Ω)) :=
    (LocalPadicLog.saturatedPadicLogEquiv (Ω := Ω) p (prime_norm_lt_one w p hpw)).symm.finiteDimensional
  rw [multiplicativeSpan_eq_units_sup_primeLine w p hpw]
  unfold primeLine
  infer_instance

theorem multiplicativeSpan_isClosed : IsClosed (multiplicativeSpan w p (Ω := Ω) : Set H) := by
  haveI : T2Space H := LocalPadicLog.rationalH1_t2 p
  haveI := multiplicativeSpan_finiteDimensional w p hpw (Ω := Ω)
  exact (multiplicativeSpan w p).closed_of_finiteDimensional

theorem integralCoefficientImage_subset_multiplicativeSpan
    (x : continuousCohomology 1 (LocalKummer.padicTateTopRep
      (K := completionAt K w) (Ω := Ω) p)) :
    LocalKummer.Rational.standardMap p x ∈ multiplicativeSpan w p := by
  obtain ⟨f, hf, hfx⟩ := ContinuousH1Recognition.classOf_surjective
    (LocalKummer.padicTateTopRep (K := completionAt K w) (Ω := Ω) p) x
  let c : LocalKummer.continuousCocycles (K := completionAt K w) (Ω := Ω) p :=
    ⟨⟨fun σ => (f σ).toMul, continuous_toMul.comp f.continuous⟩,
      fun σ τ => congrArg Additive.toMul (hf σ τ)⟩
  have hc : LocalKummer.padicClassOfCocycle p c = x := hfx
  rw [← hc, LocalKummer.Rational.standardMap_classOfCocycle]
  obtain ⟨a, ha⟩ := LocalKummer.Rational.exists_kummerClass_sequence_tendsto p c
  exact (multiplicativeSpan_isClosed w p hpw).mem_of_tendsto ha
    (Eventually.of_forall fun n => Submodule.subset_span ⟨a n, rfl⟩)

theorem multiplicativeSpan_eq_top : multiplicativeSpan w p (Ω := Ω) = ⊤ := by
  apply top_unique
  rw [← LocalKummer.Rational.span_integralCoefficientImage_eq_top (K := completionAt K w) (Ω := Ω) p]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  exact integralCoefficientImage_subset_multiplicativeSpan w p hpw x

theorem units_sup_primeLine_eq_top : unitsSubspace w p hpw (Ω := Ω) ⊔ primeLine w p = ⊤ := by
  rw [← multiplicativeSpan_eq_units_sup_primeLine, multiplicativeSpan_eq_top w p hpw]

theorem units_primeLine_isCompl : IsCompl (unitsSubspace w p hpw (Ω := Ω)) (primeLine w p) :=
  ⟨units_disjoint_primeLine w p hpw, codisjoint_iff.mpr (units_sup_primeLine_eq_top w p hpw)⟩

end
end JoshiTeich.Act1Scene1.LocalCompletion.KummerValuation
