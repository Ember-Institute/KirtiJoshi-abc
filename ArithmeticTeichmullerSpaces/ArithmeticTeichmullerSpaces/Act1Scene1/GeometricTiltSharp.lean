import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltField
import Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero

/-!
source-id: JT-SCENE1-GEOMETRIC-TILT-SHARP
source: Joshi I untilt data and Arithmetic Holomorphic Structures tilt;
Mathlib PreTilt untilt, coefficients, valuation and monoid localization.
fidelity: proves the actual sharp norm comparison from reduction and inverse
Frobenius, then extends sharp multiplicatively to the same tilt fraction
field. No norm comparison or sharp map is supplied as a certificate.
Tilt topology/completeness and a selected holomorphoid identity remain open.
Original proofs; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.GeometricTiltSharp

open JoshiTeich.Prologue
open scoped NNReal
universe u
noncomputable section
variable (Ω : Type u) [NormedField Ω] [IsUltrametricDist Ω] [CompleteSpace Ω]
variable (p : ℕ) [Fact p.Prime]
variable [hp : Fact (0 < ‖(p : Ω)‖ ∧ ‖(p : Ω)‖ < 1)]

/-- Canonical untilting, including zero, followed by the actual integer-ring inclusion. -/
def integralSharp : GeometricTiltField.Source Ω p →*₀ Ω :=
  (algebraMap (LocalGeometricFontaine.integerRing Ω) Ω).toMonoidWithZeroHom.comp
    (Perfection.teichmuller₀ p (Ideal.span {(p : LocalGeometricFontaine.integerRing Ω)}))

theorem integralSharp_eq_untilt (x : GeometricTiltField.Source Ω p) :
    integralSharp Ω p x =
      (Perfectoid.untiltMap (O := LocalGeometricFontaine.integerRing Ω) (p := p) x : Ω) := rfl

/-- Reduction of an inverse-Frobenius shift identifies the nonzero coefficient's norm. -/
theorem sourceValuation_eq_sharp_norm (x : GeometricTiltField.Source Ω p) :
    GeometricTiltField.sourceValuation Ω p x = ‖integralSharp Ω p x‖₊ := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, nnnorm_zero]
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n x ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    apply Perfection.ext
    intro n
    exact (show Perfection.coeff (ModP (LocalGeometricFontaine.integerRing Ω) p) p n x = 0
      from h n).trans (map_zero _).symm
  let y := ((frobeniusEquiv (GeometricTiltField.Source Ω p) p).symm^[n]) x
  have hcoeff : PreTilt.coeff 0 y = PreTilt.coeff n x := by
    simpa only [Nat.zero_add] using PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n x
  have hred : Ideal.Quotient.mk (Ideal.span {(p : LocalGeometricFontaine.integerRing Ω)})
      (PreTilt.untilt y) = PreTilt.coeff n x :=
    (PreTilt.mk_untilt_eq_coeff_zero y).trans hcoeff
  have hred0 : Ideal.Quotient.mk (Ideal.span {(p : LocalGeometricFontaine.integerRing Ω)})
      (PreTilt.untilt y) ≠ 0 := by rw [hred]; exact hn
  have hv : ModP.preVal Ω (NormedField.valuation (K := Ω))
      (LocalGeometricFontaine.integerRing Ω) p (PreTilt.coeff n x) =
        ‖((PreTilt.untilt y : LocalGeometricFontaine.integerRing Ω) : Ω)‖₊ := by
    rw [← hred]
    exact ModP.preVal_mk (Valuation.integer.integers _) hred0
  have hpow : ((PreTilt.untilt y : LocalGeometricFontaine.integerRing Ω) : Ω) ^ p ^ n = ((PreTilt.untilt x : LocalGeometricFontaine.integerRing Ω) : Ω) := by
    have h := congrArg (fun z : LocalGeometricFontaine.integerRing Ω => (z : Ω))
      (PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n)
    simpa only [Subring.coe_pow] using h
  change PreTilt.valAux Ω (NormedField.valuation (K := Ω))
    (LocalGeometricFontaine.integerRing Ω) p x = _
  rw [PreTilt.valAux_eq (Valuation.integer.integers _) hn, hv, ← nnnorm_pow, hpow]
  rfl

theorem integralSharp_eq_zero_iff (x : GeometricTiltField.Source Ω p) :
    integralSharp Ω p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply (GeometricTiltField.sourceValuation_eq_zero_iff Ω p x).mp
    rw [sourceValuation_eq_sharp_norm, h, nnnorm_zero]
  · rintro rfl
    exact map_zero _

theorem integralSharp_denominator_units (s : nonZeroDivisors (GeometricTiltField.Source Ω p)) :
    IsUnit (integralSharp Ω p s) :=
  isUnit_iff_ne_zero.mpr (fun h => (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
    ((integralSharp_eq_zero_iff Ω p s).mp h))

/-- The multiplicative sharp map on the actual pretilt fraction field. -/
def sharp : GeometricTiltField.FractionField Ω p →*₀ Ω :=
  (IsLocalization.toLocalizationMap (nonZeroDivisors (GeometricTiltField.Source Ω p))
    (GeometricTiltField.FractionField Ω p)).lift₀ (integralSharp Ω p)
      (integralSharp_denominator_units Ω p)

theorem sharp_inclusion (x : GeometricTiltField.Source Ω p) :
    sharp Ω p (algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p) x) =
      integralSharp Ω p x :=
  Submonoid.LocalizationMap.lift_eq _ (integralSharp_denominator_units Ω p) x

theorem sharp_div (a b : GeometricTiltField.Source Ω p) :
    sharp Ω p (algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p) a /
      algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p) b) =
        integralSharp Ω p a / integralSharp Ω p b := by
  rw [map_div₀, sharp_inclusion, sharp_inclusion]

theorem sharp_norm (x : GeometricTiltField.FractionField Ω p) :
    ‖sharp Ω p x‖₊ = GeometricTiltField.fractionValuation Ω p x := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (GeometricTiltField.Source Ω p) x
  rw [sharp_div, nnnorm_div, GeometricTiltField.fractionValuation_div,
    sourceValuation_eq_sharp_norm, sourceValuation_eq_sharp_norm]

section AlgebraicallyClosed
variable [IsAlgClosed Ω]

/-- An actual integral p-th root selected using algebraic closedness. -/
def integralRoot (x : LocalGeometricFontaine.integerRing Ω) : LocalGeometricFontaine.integerRing Ω :=
  Classical.choose (LocalGeometricFontaine.integral_pow_surjective Ω p (Fact.out : p.Prime).pos x)

omit hp [CompleteSpace Ω] in
theorem integralRoot_pow (x : LocalGeometricFontaine.integerRing Ω) :
    integralRoot Ω p x ^ p = x :=
  Classical.choose_spec (LocalGeometricFontaine.integral_pow_surjective Ω p (Fact.out : p.Prime).pos x)

def rootTower (x : LocalGeometricFontaine.integerRing Ω) : ℕ → LocalGeometricFontaine.integerRing Ω
  | 0 => x
  | n + 1 => integralRoot Ω p (rootTower x n)

omit hp [CompleteSpace Ω] in
theorem rootTower_pow (x : LocalGeometricFontaine.integerRing Ω) (n : ℕ) :
    rootTower Ω p x n ^ p ^ n = x := by
  induction n with
  | zero => simp only [rootTower, pow_zero, pow_one]
  | succ n ih => rw [pow_succ', pow_mul, rootTower, integralRoot_pow, ih]

/-- A pretilt element from the compatible actual p-power roots of an integral element. -/
def rootLift (x : LocalGeometricFontaine.integerRing Ω) : GeometricTiltField.Source Ω p :=
  ⟨fun n => Ideal.Quotient.mk (Ideal.span {(p : LocalGeometricFontaine.integerRing Ω)})
    (rootTower Ω p x n), fun n => by
      rw [← map_pow]
      exact congrArg (Ideal.Quotient.mk _) (integralRoot_pow Ω p (rootTower Ω p x n))⟩

theorem untilt_rootLift (x : LocalGeometricFontaine.integerRing Ω) :
    PreTilt.untilt (rootLift Ω p x) = x := by
  change Perfection.teichmuller p (Ideal.span {(p : LocalGeometricFontaine.integerRing Ω)})
    (rootLift Ω p x) = x
  apply Perfection.teichmuller_spec
  intro n
  refine ⟨rootTower Ω p x n, rfl, ?_⟩
  simp only [rootTower_pow, SModEq.refl]

theorem integralSharp_rootLift (x : LocalGeometricFontaine.integerRing Ω) :
    integralSharp Ω p (rootLift Ω p x) = (x : Ω) := by
  rw [integralSharp_eq_untilt]
  change ((PreTilt.untilt (rootLift Ω p x) : LocalGeometricFontaine.integerRing Ω) : Ω) = (x : Ω)
  rw [untilt_rootLift]

/-- Every field element is a quotient of sharp images of integral compatible-root towers. -/
theorem sharp_surjective : Function.Surjective (sharp Ω p) := by
  intro x
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero]⟩
  have hxpos := norm_pos_iff.mpr hx
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hxpos) hp.out.2
  let b : LocalGeometricFontaine.integerRing Ω := (p : LocalGeometricFontaine.integerRing Ω) ^ n
  have hb : (b : Ω) ≠ 0 := pow_ne_zero n (norm_pos_iff.mp hp.out.1)
  have ha : (b : Ω) * x ∈ LocalGeometricFontaine.integerRing Ω := by
    rw [LocalGeometricFontaine.mem_integerRing]
    change ‖(p : Ω) ^ n * x‖ ≤ 1
    rw [norm_mul, norm_pow]
    exact ((lt_div_iff₀ hxpos).mp hn).le
  let a : LocalGeometricFontaine.integerRing Ω := ⟨(b : Ω) * x, ha⟩
  refine ⟨algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p)
      (rootLift Ω p a) /
    algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p)
      (rootLift Ω p b), ?_⟩
  rw [sharp_div, integralSharp_rootLift, integralSharp_rootLift]
  change ((b : Ω) * x) / (b : Ω) = x
  exact (div_eq_iff hb).mpr (mul_comm _ _)

end AlgebraicallyClosed

/-- Sharp on a fixed constructed tilt carrier, with proved source and norm identities. -/
structure Data (A : GeometricTiltField.Data (GeometricTiltField.Source Ω p) p) where
  map : letI := A.field
    A.Carrier →*₀ Ω
  norm_map : letI := A.field
    ∀ x, ‖map x‖₊ = A.valuation x
  surjective : letI := A.field
    Function.Surjective map
  on_integral : letI := A.field
    ∀ x, map (A.inclusion x) = integralSharp Ω p x

variable [IsAlgClosed Ω]

def ofField : Data Ω p (GeometricTiltField.ofField Ω p) where
  map := sharp Ω p
  norm_map := sharp_norm Ω p
  surjective := sharp_surjective Ω p
  on_integral := sharp_inclusion Ω p

end
end JoshiTeich.Act1Scene1.GeometricTiltSharp
