import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionAmbientKummerLog

/-!
source-id: JT-SCENE1-COMPLETION-KUMMER-COORDINATES
source: original continuous H1, completion Kummer span, unit logarithm and
residue-prime valuation; Joshi III 3190--3236 as local comparison background.
fidelity: gives continuous linear coordinates (ordinary log, prime coefficient)
on the original H1 topology. Computes the valuation coordinate on every field
Kummer class. This does not identify the unit kernel with H1e or Bloch--Kato.
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
local instance coordinatesCharZero : CharZero (completionAt K w) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective
local notation "H" => continuousCohomology 1 (LocalKummer.Rational.topRep
  (K := completionAt K w) (Ω := Ω) p)
local notation "U" => unitsSubspace w p hpw (Ω := Ω)
local notation "P" => primeLine w p (Ω := Ω)
include hpw

theorem rationalH1_finiteDimensional : FiniteDimensional ℚ_[p] H := by
  haveI : FiniteDimensional ℚ_[p] (⊤ : Submodule ℚ_[p] H) := by
    rw [← multiplicativeSpan_eq_top w p hpw]
    exact multiplicativeSpan_finiteDimensional w p hpw
  exact (Submodule.topEquiv : (⊤ : Submodule ℚ_[p] H) ≃ₗ[ℚ_[p]] H).finiteDimensional

theorem prime_kummer_ne_zero : kummer w p (Ω := Ω) (primeUnit w p) ≠ 0 := by
  intro h
  apply prime_kummer_not_mem_units w p hpw (Ω := Ω)
  rw [h]
  exact (U).zero_mem

def primeLineEquiv : ℚ_[p] ≃ₗ[ℚ_[p]] P :=
  LinearEquiv.toSpanNonzeroSingleton ℚ_[p] H (kummer w p (primeUnit w p))
    (prime_kummer_ne_zero w p hpw)

variable [Algebra ℚ_[p] (completionAt K w)]
variable [ContinuousSMul ℚ_[p] (completionAt K w)]

def kummerCoordinates : H ≃ₗ[ℚ_[p]] (completionAt K w × ℚ_[p]) :=
  ((U).prodEquivOfIsCompl P (units_primeLine_isCompl w p hpw)).symm.trans
    ((LocalPadicLog.saturatedPadicLogEquiv p (prime_norm_lt_one w p hpw)).prodCongr
      (primeLineEquiv w p hpw).symm)

theorem kummerCoordinates_fst (x : H) :
    (kummerCoordinates w p hpw x).1 = ambientLog w p hpw x := rfl

def valuationCoordinate : H →ₗ[ℚ_[p]] ℚ_[p] :=
  (LinearMap.snd ℚ_[p] (completionAt K w) ℚ_[p]).comp
    (kummerCoordinates w p hpw).toLinearMap

theorem kummerCoordinates_unit (x : U) :
    kummerCoordinates w p hpw (x : H) =
      (LocalPadicLog.saturatedPadicLog p (prime_norm_lt_one w p hpw) x, 0) := by
  change ((LocalPadicLog.saturatedPadicLogEquiv p (prime_norm_lt_one w p hpw)).prodCongr
    (primeLineEquiv w p hpw).symm)
      (((U).prodEquivOfIsCompl P (units_primeLine_isCompl w p hpw)).symm x) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  apply Prod.ext
  · rfl
  · exact (primeLineEquiv w p hpw).symm.map_zero

theorem kummerCoordinates_prime :
    kummerCoordinates w p hpw (kummer w p (Ω := Ω) (primeUnit w p)) = (0, 1) := by
  let x : P := ⟨kummer w p (primeUnit w p), Submodule.mem_span_singleton_self _⟩
  change ((LocalPadicLog.saturatedPadicLogEquiv p (prime_norm_lt_one w p hpw)).prodCongr
    (primeLineEquiv w p hpw).symm)
      (((U).prodEquivOfIsCompl P (units_primeLine_isCompl w p hpw)).symm (x : H)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
  apply Prod.ext
  · exact (LocalPadicLog.saturatedPadicLogEquiv p (prime_norm_lt_one w p hpw)).map_zero
  · exact LinearEquiv.coord_self ℚ_[p] H _ (prime_kummer_ne_zero w p hpw)

theorem valuationCoordinate_unit (x : U) : valuationCoordinate w p hpw (x : H) = 0 :=
  congrArg Prod.snd (kummerCoordinates_unit w p hpw x)

theorem valuationCoordinate_prime :
    valuationCoordinate w p hpw (kummer w p (Ω := Ω) (primeUnit w p)) = 1 :=
  congrArg Prod.snd (kummerCoordinates_prime w p hpw)

theorem valuationCoordinate_eq_zero_iff (x : H) :
    valuationCoordinate w p hpw x = 0 ↔ x ∈ U := by
  change (primeLineEquiv w p hpw).symm
    (((U).prodEquivOfIsCompl P (units_primeLine_isCompl w p hpw)).symm x).2 = 0 ↔ _
  exact ((primeLineEquiv w p hpw).symm.map_eq_zero_iff).trans
    (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero U P (units_primeLine_isCompl w p hpw))

theorem valuationCoordinate_kummer (a : (completionAt K w)ˣ) :
    valuationCoordinate w p hpw (kummer w p (Ω := Ω) a) =
      -((valuationIndex w a : ℚ_[p]) / Arithmetic.ramIdx w) := by
  rw [kummer_decomposition w p a, map_sub, map_smul, map_smul,
    valuationCoordinate_unit w p hpw
      ⟨kummer w p (Ω := Ω) (correctedUnit w p a), correctedUnit_kummer_mem w p hpw a⟩,
    valuationCoordinate_prime, smul_zero, zero_sub, smul_eq_mul, mul_one]

/-- This equivalence retains both original topologies. -/
def kummerCoordinatesContinuousEquiv : H ≃L[ℚ_[p]] (completionAt K w × ℚ_[p]) := by
  haveI := rationalH1_finiteDimensional w p hpw (Ω := Ω)
  haveI : T2Space H := LocalPadicLog.rationalH1_t2 p
  exact (kummerCoordinates w p hpw).toContinuousLinearEquiv

theorem ambientLog_continuous : Continuous (ambientLog w p hpw (Ω := Ω)) := by
  exact continuous_fst.comp (kummerCoordinatesContinuousEquiv w p hpw).continuous

theorem valuationCoordinate_continuous : Continuous (valuationCoordinate w p hpw (Ω := Ω)) := by
  exact continuous_snd.comp (kummerCoordinatesContinuousEquiv w p hpw).continuous

theorem rationalH1_finrank : Module.finrank ℚ_[p] H =
    Module.finrank ℚ_[p] (completionAt K w) + 1 := by
  haveI := rationalH1_finiteDimensional w p hpw (Ω := Ω)
  haveI := (kummerCoordinates w p hpw (Ω := Ω)).finiteDimensional
  haveI : FiniteDimensional ℚ_[p] (completionAt K w) :=
    FiniteDimensional.of_surjective
      (LinearMap.fst ℚ_[p] (completionAt K w) ℚ_[p]) (fun x => ⟨(x, 0), rfl⟩)
  rw [(kummerCoordinates w p hpw (Ω := Ω)).finrank_eq, Module.finrank_prod,
    Module.finrank_self]

end
end JoshiTeich.Act1Scene1.LocalCompletion.KummerValuation
