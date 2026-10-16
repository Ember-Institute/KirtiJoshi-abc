import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionKummerSpan
import Mathlib.LinearAlgebra.Projection

/-!
source-id: JT-SCENE1-COMPLETION-AMBIENT-KUMMER-LOG
source: the completion unit/prime complement and ordinary saturated Kummer
logarithm; Joshi III 3190--3236, with the explicit branch log(p) = 0.
fidelity: extends the existing ordinary logarithm to the original rational
continuous H1. Its kernel is exactly the prime line. The branch is uniquely
determined by its unit restriction and its value on p. No H1e/BK identity.
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
local instance ambientCharZero : CharZero (completionAt K w) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective
variable [Algebra ℚ_[p] (completionAt K w)]
variable [ContinuousSMul ℚ_[p] (completionAt K w)]
local notation "H" => continuousCohomology 1 (LocalKummer.Rational.topRep
  (K := completionAt K w) (Ω := Ω) p)
local notation "U" => unitsSubspace w p hpw (Ω := Ω)
local notation "P" => primeLine w p (Ω := Ω)

/-- The prime branch is fixed explicitly, rather than inferred from unit log. -/
def ambientLog : H →ₗ[ℚ_[p]] completionAt K w :=
  (LocalPadicLog.saturatedPadicLog p (prime_norm_lt_one w p hpw)).comp
    ((U).projectionOnto P (units_primeLine_isCompl w p hpw))

theorem ambientLog_unit (x : U) :
    ambientLog w p hpw (x : H) =
      LocalPadicLog.saturatedPadicLog p (prime_norm_lt_one w p hpw) x := by
  change LocalPadicLog.saturatedPadicLog p (prime_norm_lt_one w p hpw)
    ((U).projectionOnto P (units_primeLine_isCompl w p hpw) x) = _
  rw [Submodule.projectionOnto_apply_left]

theorem ambientLog_eq_zero_iff (x : H) :
    ambientLog w p hpw x = 0 ↔ x ∈ P := by
  let E : U ≃ₗ[ℚ_[p]] completionAt K w :=
    LocalPadicLog.saturatedPadicLogEquiv p (prime_norm_lt_one w p hpw)
  change E ((U).projectionOnto P (units_primeLine_isCompl w p hpw) x) = 0 ↔ _
  constructor
  · intro hx
    exact (Submodule.projectionOnto_apply_eq_zero_iff
      (units_primeLine_isCompl w p hpw)).mp (E.injective (hx.trans E.map_zero.symm))
  · intro hx
    exact (congrArg E ((Submodule.projectionOnto_apply_eq_zero_iff
      (units_primeLine_isCompl w p hpw)).mpr hx)).trans E.map_zero

theorem ambientLog_prime :
    ambientLog w p hpw (kummer w p (Ω := Ω) (primeUnit w p)) = 0 :=
  (ambientLog_eq_zero_iff w p hpw _).mpr
    (Submodule.mem_span_singleton_self _)

theorem ambientLog_ker : LinearMap.ker (ambientLog w p hpw (Ω := Ω)) = P := by
  ext x
  exact ambientLog_eq_zero_iff w p hpw x

theorem ambientLog_surjective : Function.Surjective (ambientLog w p hpw (Ω := Ω)) := by
  intro z
  let x := (LocalPadicLog.saturatedPadicLogEquiv (Ω := Ω) p
    (prime_norm_lt_one w p hpw)).symm z
  refine ⟨x, (ambientLog_unit w p hpw x).trans ?_⟩
  exact (LocalPadicLog.saturatedPadicLogEquiv p
    (prime_norm_lt_one w p hpw)).apply_symm_apply z

theorem ambientLog_kummer (a : (completionAt K w)ˣ) :
    ambientLog w p hpw (kummer w p (Ω := Ω) a) =
      (Arithmetic.ramIdx w : ℚ_[p])⁻¹ •
        LocalPadicLog.saturatedPadicLog p (prime_norm_lt_one w p hpw)
          ⟨kummer w p (Ω := Ω) (correctedUnit w p a), correctedUnit_kummer_mem w p hpw a⟩ := by
  rw [kummer_decomposition w p a, map_sub, map_smul, map_smul,
    ambientLog_prime, smul_zero, sub_zero]
  congr 1
  exact ambientLog_unit w p hpw
    ⟨kummer w p (Ω := Ω) (correctedUnit w p a), correctedUnit_kummer_mem w p hpw a⟩

theorem ambientLog_unique (L : H →ₗ[ℚ_[p]] completionAt K w)
    (hU : ∀ x : U, L x =
      LocalPadicLog.saturatedPadicLog p (prime_norm_lt_one w p hpw) x)
    (hP : L (kummer w p (primeUnit w p)) = 0) : L = ambientLog w p hpw := by
  ext x
  let u := (U).projectionOnto P (units_primeLine_isCompl w p hpw) x
  let v := (P).projectionOnto U (units_primeLine_isCompl w p hpw).symm x
  have hx : (u : H) + (v : H) = x :=
    Submodule.projection_add_projection_eq_self (units_primeLine_isCompl w p hpw) x
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp v.2
  have hv : L (v : H) = 0 := by rw [← hc, map_smul, hP, smul_zero]
  have hv' : ambientLog w p hpw (v : H) = 0 :=
    (ambientLog_eq_zero_iff w p hpw _).mpr v.2
  rw [← hx, map_add, map_add, hv, hv', add_zero, add_zero,
    hU u, ambientLog_unit w p hpw u]

end
end JoshiTeich.Act1Scene1.LocalCompletion.KummerValuation
