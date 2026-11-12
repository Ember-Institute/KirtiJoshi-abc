import ArithmeticTeichmullerSpaces.Act1Scene1.AdicLogarithm
import ArithmeticTeichmullerSpaces.Compatibility.PowerSeriesExpLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
source-id: JT-SCENE1-ADIC-EXPONENTIAL
source: Joshi II multiplicative-formal-group Tate module (935--958);
Mathlib rational formal exp/log, substitution and convergent evaluation.
fidelity: evaluates rational formal identities in the original complete
linearly topologized Q-algebra. Proves exp/log inverses and the exponential
addition law. The discrete topology is local to the rational coefficients;
the target ring keeps its given topology. Original proofs;
Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.AdicExponential

noncomputable section
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology
local instance rationalUniform : UniformSpace ℚ := ⊥
variable (R : Type*) [CommRing R] [Algebra ℚ R]
variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
variable [IsLinearTopology R R] [CompleteSpace R] [T2Space R]

def evaluate (a : R) (ha : PowerSeries.HasEval a) : PowerSeries ℚ →+* R :=
  PowerSeries.eval₂Hom (φ := algebraMap ℚ R) (continuous_of_discreteTopology) ha

theorem continuous_evaluate (a : R) (ha : PowerSeries.HasEval a) :
    Continuous (evaluate R a ha) := by
  simpa only [evaluate, PowerSeries.coe_eval₂Hom] using
    PowerSeries.continuous_eval₂ (φ := algebraMap ℚ R) continuous_of_discreteTopology ha

theorem evaluate_X (a : R) (ha : PowerSeries.HasEval a) : evaluate R a ha PowerSeries.X = a := by
  simpa only [evaluate, PowerSeries.coe_eval₂Hom] using
    PowerSeries.eval₂_X (algebraMap ℚ R) a

theorem evaluate_log (a : R) (ha : PowerSeries.HasEval a) :
    evaluate R a ha (PowerSeries.log ℚ) = AdicLogarithm.oneAdd R a ha := by
  have hc (n : ℕ) : algebraMap ℚ R (PowerSeries.coeff n (PowerSeries.log ℚ)) =
      PowerSeries.coeff n (PowerSeries.log R) := by
    rw [← PowerSeries.map_log (algebraMap ℚ R), PowerSeries.coeff_map]
  have h := PowerSeries.hasSum_eval₂ (φ := algebraMap ℚ R)
    continuous_of_discreteTopology ha (PowerSeries.log ℚ)
  have he : HasSum (fun n => PowerSeries.coeff n (PowerSeries.log R) * a ^ n)
      (evaluate R a ha (PowerSeries.log ℚ)) := by
    simpa only [hc, evaluate, PowerSeries.coe_eval₂Hom] using h
  exact he.unique (AdicLogarithm.hasSum_oneAdd R a ha)

theorem evaluate_subst (a : R) (ha : PowerSeries.HasEval a)
    (g : PowerSeries ℚ) (hg : PowerSeries.HasSubst g) (f : PowerSeries ℚ) :
    evaluate R a ha (f.subst g) =
      evaluate R (evaluate R a ha g) (hg.hasEval.map (continuous_evaluate R a ha)) f := by
  have h := MvPowerSeries.eval₂_subst (R := ℚ) (S := ℚ) (T := R)
    (a := fun _ : Unit => g) hg.const (b := fun _ : Unit => a) (PowerSeries.hasEval ha) f
  simpa only [PowerSeries.subst, PowerSeries.eval₂, evaluate, PowerSeries.coe_eval₂Hom] using h

def exp (a : R) (ha : PowerSeries.HasEval a) : R := evaluate R a ha (PowerSeries.exp ℚ)

theorem hasEval_log (a : R) (ha : PowerSeries.HasEval a) :
    PowerSeries.HasEval (AdicLogarithm.oneAdd R a ha) := by
  obtain ⟨u, hu⟩ := AdicLogarithm.oneAdd_eq_mul_unit R a ha
  rw [hu]
  exact PowerSeries.HasEval.mul_right (u : R) ha

theorem exp_log (a : R) (ha : PowerSeries.HasEval a) :
    exp R (AdicLogarithm.oneAdd R a ha) (hasEval_log R a ha) = 1 + a := by
  have h := evaluate_subst R a ha (PowerSeries.log ℚ) PowerSeries.HasSubst.log (PowerSeries.exp ℚ)
  simpa only [Compatibility.PowerSeriesExpLog.subst_exp_log, map_add, map_one, evaluate_X,
    evaluate_log, exp] using h.symm

theorem hasEval_exp_sub_one (a : R) (ha : PowerSeries.HasEval a) :
    PowerSeries.HasEval (exp R a ha - 1) := by
  have h := (PowerSeries.HasSubst.exp_sub_one (A := ℚ)).hasEval.map (continuous_evaluate R a ha)
  simpa only [map_sub, map_one, exp] using h

theorem log_exp (a : R) (ha : PowerSeries.HasEval a) :
    AdicLogarithm.oneAdd R (exp R a ha - 1) (hasEval_exp_sub_one R a ha) = a := by
  have h := evaluate_subst R a ha (PowerSeries.exp ℚ - 1)
    PowerSeries.HasSubst.exp_sub_one (PowerSeries.log ℚ)
  simpa only [Compatibility.PowerSeriesExpLog.subst_log_exp_sub_one, evaluate_X, map_sub, map_one,
    evaluate_log, exp] using h.symm

/-- The bivariate identity is proved on rational coefficients before evaluation. -/
theorem formal_exp_add :
    PowerSeries.subst ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) ℚ) +
        MvPowerSeries.X (1 : Fin 2))
        (PowerSeries.exp ℚ) =
      PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) (PowerSeries.exp ℚ) *
        PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) (PowerSeries.exp ℚ) := by
  ext e
  rw [PowerSeries.coeff_subst_X_zero_add_X_one,
    PowerSeries.coeff_subst_X_zero_subst_mul_X_one]
  simp only [PowerSeries.coeff_exp, Algebra.algebraMap_self_apply]
  have hn : (e 0 + e 1).choose (e 0) * (e 0).factorial * (e 1).factorial =
      (e 0 + e 1).factorial := by
    simpa only [Nat.add_comm, mul_assoc, mul_comm, mul_left_comm] using
      Nat.add_choose_mul_factorial_mul_factorial (e 1) (e 0)
  have h : ((e 0 + e 1).choose (e 0) : ℚ) * (e 0).factorial * (e 1).factorial =
      (e 0 + e 1).factorial := by exact_mod_cast hn
  have h0 : ((e 0).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h1 : ((e 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hs : ((e 0 + e 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  convert h using 1

theorem exp_add (a b : R) (ha : PowerSeries.HasEval a) (hb : PowerSeries.HasEval b) :
    exp R (a + b) (ha.add hb) = exp R a ha * exp R b hb := by
  let v : Fin 2 → R := ![a, b]
  have hv : MvPowerSeries.HasEval v := by
    constructor
    · intro i
      fin_cases i
      · exact ha
      · exact hb
    · simp
  let E := MvPowerSeries.eval₂Hom (φ := algebraMap ℚ R) continuous_of_discreteTopology hv
  have hE : Continuous E := by
    simpa only [E, MvPowerSeries.coe_eval₂Hom] using
      MvPowerSeries.continuous_eval₂ (φ := algebraMap ℚ R) continuous_of_discreteTopology hv
  have hsub (g : MvPowerSeries (Fin 2) ℚ) (hg : PowerSeries.HasSubst g) :
      E (PowerSeries.subst g (PowerSeries.exp ℚ)) =
        exp R (E g) (hg.hasEval.map hE) := by
    have h := MvPowerSeries.eval₂_subst (R := ℚ) (S := ℚ) (T := R)
      (a := fun _ : Unit => g) hg.const hv (PowerSeries.exp ℚ)
    simpa only [E, PowerSeries.subst, PowerSeries.eval₂, evaluate,
      PowerSeries.coe_eval₂Hom, MvPowerSeries.coe_eval₂Hom, exp] using h
  have h0 : E (MvPowerSeries.X (0 : Fin 2)) = a := by
    simpa only [E, MvPowerSeries.coe_eval₂Hom, v, Matrix.cons_val_zero] using
      MvPowerSeries.eval₂_X (algebraMap ℚ R) v (0 : Fin 2)
  have h1 : E (MvPowerSeries.X (1 : Fin 2)) = b := by
    simpa only [E, MvPowerSeries.coe_eval₂Hom, v, Matrix.cons_val_one,
      Matrix.cons_val_zero] using MvPowerSeries.eval₂_X (algebraMap ℚ R) v (1 : Fin 2)
  have h := congrArg E formal_exp_add
  rw [map_mul, hsub _ (PowerSeries.HasSubst.X _), hsub _ (PowerSeries.HasSubst.X _),
    hsub _ ((PowerSeries.HasSubst.X _).add (PowerSeries.HasSubst.X _))] at h
  simpa only [map_add, h0, h1] using h

end
end JoshiTeich.Act1Scene1.AdicExponential
