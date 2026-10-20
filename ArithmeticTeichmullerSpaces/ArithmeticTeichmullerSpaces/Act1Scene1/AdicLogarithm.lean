import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Log

/-!
source-id: JT-SCENE1-ADIC-LOGARITHM
source: Joshi II multiplicative-formal-group Tate period (935--958);
Mathlib formal logarithm and evaluation in a complete linearly topologized ring.
fidelity: constructs the convergent formal logarithm at a topologically
nilpotent element of a complete Q-algebra. Proves it is the input times a
unit, hence preserves nonvanishing and ideal membership. No norm or
period-ring identity is supplied as an assumption. Original proofs;
Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.AdicLogarithm

noncomputable section
variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The formal quotient log(1+X)/X, with constant coefficient one. -/
def quotient : PowerSeries R :=
  PowerSeries.mk fun n => PowerSeries.coeff (n + 1) (PowerSeries.log R)

theorem log_eq_X_mul_quotient :
    PowerSeries.log R = PowerSeries.X * quotient R := by
  simpa only [PowerSeries.constantCoeff_log, map_zero, add_zero, quotient] using
    PowerSeries.eq_X_mul_shift_add_const (PowerSeries.log R)

theorem constantCoeff_quotient : PowerSeries.constantCoeff (quotient R) = 1 := by
  simp only [quotient, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_mk, zero_add, PowerSeries.coeff_one_log]

theorem isUnit_quotient : IsUnit (quotient R) :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_quotient]; exact isUnit_one)

variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
variable [IsLinearTopology R R] [CompleteSpace R] [T2Space R]

/-- The actual evaluation of the formal logarithm in the original complete ring. -/
def oneAdd (a : R) (ha : PowerSeries.HasEval a) : R :=
  PowerSeries.eval₂Hom (φ := RingHom.id R) continuous_id ha (PowerSeries.log R)

theorem hasSum_oneAdd (a : R) (ha : PowerSeries.HasEval a) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.log R) * a ^ n)
      (oneAdd R a ha) := by
  simpa only [RingHom.id_apply, oneAdd, PowerSeries.coe_eval₂Hom] using
    PowerSeries.hasSum_eval₂ (φ := RingHom.id R) continuous_id ha (PowerSeries.log R)

theorem oneAdd_eq_mul_unit (a : R) (ha : PowerSeries.HasEval a) :
    ∃ u : Rˣ, oneAdd R a ha = a * u := by
  let E := PowerSeries.eval₂Hom (φ := RingHom.id R) continuous_id ha
  obtain ⟨u, hu⟩ := (isUnit_quotient R).map E
  refine ⟨u, ?_⟩
  change E (PowerSeries.log R) = a * u
  rw [log_eq_X_mul_quotient, map_mul]
  have hX : E PowerSeries.X = a := by
    simpa only [E, PowerSeries.coe_eval₂Hom] using PowerSeries.eval₂_X (RingHom.id R) a
  rw [hX, hu]

theorem oneAdd_eq_zero_iff (a : R) (ha : PowerSeries.HasEval a) :
    oneAdd R a ha = 0 ↔ a = 0 := by
  obtain ⟨u, hu⟩ := oneAdd_eq_mul_unit R a ha
  rw [hu, u.mul_left_eq_zero]

theorem oneAdd_mem_ideal (I : Ideal R) (a : R) (ha : PowerSeries.HasEval a)
    (hI : a ∈ I) : oneAdd R a ha ∈ I := by
  obtain ⟨u, hu⟩ := oneAdd_eq_mul_unit R a ha
  rw [hu]
  simpa only [mul_comm] using I.mul_mem_left (u : R) hI

end
end JoshiTeich.Act1Scene1.AdicLogarithm
