import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionKummerCoordinates

/-!
source-id: JT-SCENE1-COMPLETION-TATE-KUMMER-LOG
source: actual unit/valuation coordinates in rational continuous H1;
Joshi III 3150--3156 distinguishes Tate classes from unit classes.
fidelity: for any class outside the unit subspace, constructs the logarithm
that kills its line and keeps the ordinary unit logarithm. The quotient by
that line is continuously linearly equivalent to the actual completion.
This is an explicit local branch construction, not a BK or period theorem.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.KummerValuation
open NumberField JoshiTeich.Prologue
universe u v
noncomputable section
variable {K : Type u} [Field K] [NumberField K] (w : FinitePlace K)
variable (p : ℕ) [Fact p.Prime] (hpw : Arithmetic.residueChar w = p)
variable {Ω : Type v} [Field Ω] [Algebra (completionAt K w) Ω]
variable [IsGalois (completionAt K w) Ω] [Algebra.IsIntegral (completionAt K w) Ω]
variable [CharZero Ω] [IsAlgClosed Ω]
local instance tateLogCharZero : CharZero (completionAt K w) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective
variable [Algebra ℚ_[p] (completionAt K w)]
variable [ContinuousSMul ℚ_[p] (completionAt K w)]
local notation "H" => continuousCohomology 1 (LocalKummer.Rational.topRep
  (K := completionAt K w) (Ω := Ω) p)
local notation "U" => unitsSubspace w p hpw (Ω := Ω)
theorem nonunit_valuationCoordinate_ne_zero (q : H) (hq : q ∉ U) :
    valuationCoordinate w p hpw q ≠ 0 :=
  fun h => hq ((valuationCoordinate_eq_zero_iff w p hpw q).mp h)

theorem valuationCorrection_mem_units (q : H) (hq : q ∉ U) (x : H) :
    x - (valuationCoordinate w p hpw x / valuationCoordinate w p hpw q) • q ∈ U := by
  apply (valuationCoordinate_eq_zero_iff w p hpw _).mp
  rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _
    (nonunit_valuationCoordinate_ne_zero w p hpw q hq), sub_self]

theorem units_nonunitLine_isCompl (q : H) (hq : q ∉ U) : IsCompl U (ℚ_[p] ∙ q) := by
  refine ⟨Submodule.disjoint_span_singleton_of_notMem hq, codisjoint_iff.mpr ?_⟩
  apply top_unique
  intro x _
  let c := valuationCoordinate w p hpw x / valuationCoordinate w p hpw q
  exact Submodule.mem_sup.mpr
    ⟨x - c • q, valuationCorrection_mem_units w p hpw q hq x,
      c • q, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩, sub_add_cancel _ _⟩

def tateLog (q : H) (hq : q ∉ U) : H →ₗ[ℚ_[p]] completionAt K w :=
  (LocalPadicLog.saturatedPadicLog p (prime_norm_lt_one w p hpw)).comp
    ((U).projectionOnto (ℚ_[p] ∙ q) (units_nonunitLine_isCompl w p hpw q hq))

theorem tateLog_unit (q : H) (hq : q ∉ U) (x : U) :
    tateLog w p hpw q hq (x : H) =
      LocalPadicLog.saturatedPadicLog p (prime_norm_lt_one w p hpw) x := by
  change LocalPadicLog.saturatedPadicLog p (prime_norm_lt_one w p hpw)
    ((U).projectionOnto (ℚ_[p] ∙ q) (units_nonunitLine_isCompl w p hpw q hq) x) = _
  rw [Submodule.projectionOnto_apply_left]

theorem tateLog_eq_zero_iff (q : H) (hq : q ∉ U) (x : H) :
    tateLog w p hpw q hq x = 0 ↔ x ∈ ℚ_[p] ∙ q := by
  let E : U ≃ₗ[ℚ_[p]] completionAt K w :=
    LocalPadicLog.saturatedPadicLogEquiv p (prime_norm_lt_one w p hpw)
  change E ((U).projectionOnto (ℚ_[p] ∙ q)
    (units_nonunitLine_isCompl w p hpw q hq) x) = 0 ↔ _
  exact E.map_eq_zero_iff.trans
    (Submodule.projectionOnto_apply_eq_zero_iff (units_nonunitLine_isCompl w p hpw q hq))

theorem tateLog_q (q : H) (hq : q ∉ U) : tateLog w p hpw q hq q = 0 :=
  (tateLog_eq_zero_iff w p hpw q hq q).mpr (Submodule.mem_span_singleton_self q)

theorem tateLog_eq_ambientLog_sub (q : H) (hq : q ∉ U) (x : H) :
    tateLog w p hpw q hq x = ambientLog w p hpw x -
      (valuationCoordinate w p hpw x / valuationCoordinate w p hpw q) •
        ambientLog w p hpw q := by
  let y : U := ⟨_, valuationCorrection_mem_units w p hpw q hq x⟩
  have h := (tateLog_unit w p hpw q hq y).trans (ambientLog_unit w p hpw y).symm
  change tateLog w p hpw q hq
    (x - (valuationCoordinate w p hpw x / valuationCoordinate w p hpw q) • q) =
    ambientLog w p hpw
    (x - (valuationCoordinate w p hpw x / valuationCoordinate w p hpw q) • q) at h
  simpa only [map_sub, map_smul, tateLog_q, smul_zero, sub_zero] using h

/-- The quotient retains its original quotient topology. -/
def tateQuotientLogEquiv (q : H) (hq : q ∉ U) :
    (H ⧸ (ℚ_[p] ∙ q)) ≃L[ℚ_[p]] completionAt K w := by
  haveI := rationalH1_finiteDimensional w p hpw (Ω := Ω)
  haveI : T2Space H := LocalPadicLog.rationalH1_t2 p
  haveI : IsClosed (ℚ_[p] ∙ q : Set H) :=
    (ℚ_[p] ∙ q : Submodule ℚ_[p] H).closed_of_finiteDimensional
  exact (((ℚ_[p] ∙ q : Submodule ℚ_[p] H).quotientEquivOfIsCompl U
    (units_nonunitLine_isCompl w p hpw q hq).symm).trans
    (LocalPadicLog.saturatedPadicLogEquiv p (prime_norm_lt_one w p hpw))).toContinuousLinearEquiv

theorem tateQuotientLogEquiv_mk (q : H) (hq : q ∉ U) (x : H) :
    tateQuotientLogEquiv w p hpw q hq (Submodule.Quotient.mk x) =
      tateLog w p hpw q hq x := rfl

theorem tateLog_continuous (q : H) (hq : q ∉ U) :
    Continuous (tateLog w p hpw q hq) := by
  haveI := rationalH1_finiteDimensional w p hpw (Ω := Ω)
  haveI : T2Space H := LocalPadicLog.rationalH1_t2 p
  exact (tateLog w p hpw q hq).continuous_of_finiteDimensional

end
end JoshiTeich.Act1Scene1.LocalCompletion.KummerValuation
