import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionAlgebraNormGeneral
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionDegree
import ArithmeticTeichmullerSpaces.Act1Scene1.CompletedAlgebraicClosure
import ArithmeticTeichmullerSpaces.Act1Scene1.PositivePowerCalibration
import Mathlib.NumberTheory.Padics.Complex

/-!
source-id: JT-SCENE1-LOCAL-COMPLETION-ALGEBRAIC-PADIC-NORM
source: Joshi II `se:ff-rings`, with its fixed coefficient field C_p^flat;
the actual local algebraic-norm and degree identities, and Mathlib's
uniqueness of the spectral algebra norm.
fidelity: the original completion norm restricts to the local-degree power
of the standard Q_p norm. On its algebraic closure, the
reciprocal-degree power of the original norm is a multiplicative Q_p
algebra norm and equals the spectral norm. Algebraic-closure uniqueness
then constructs an equivalence with the standard p-adic algebraic closure;
the norm power law extends it to the completed algebraic closures.
boundary: Scene1/Derived; the completed coefficient comparison retains the
original norm and its local-degree calibration. It does not identify the
tilt or the period completion with paper B. Original proofs; no reference
code copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion

open NumberField JoshiTeich.Prologue.Arithmetic
noncomputable section

private theorem isClosed_norm_pow_eq_norm {E F : Type*}
    [TopologicalSpace E] [TopologicalSpace F] [Norm E] [Norm F]
    (hE : Continuous (fun x : E => ‖x‖)) (hF : Continuous (fun y : F => ‖y‖))
    (f : E → F) (hf : Continuous f) (n : ℕ) :
    IsClosed {x : E | ‖f x‖ ^ n = ‖x‖} :=
  isClosed_eq ((hF.comp hf).pow n) hE

universe u
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable (w : FinitePlace K) (hw : residueChar w = p)

theorem norm_padicEmb_eq_pow (a : ℚ_[p]) :
    ‖padicEmb hw a‖ = ‖a‖ ^ localDeg w := by
  let := padicAlgebra hw
  let : Module.Finite ℚ_[p] (completionAt K w) := finite_padicAlgebra hw
  by_cases ha : a = 0
  · simp only [ha, map_zero, norm_zero, zero_pow (localDeg_pos w).ne']
  have h := norm_algebraNorm_eq_completionNorm w hw (padicEmb hw a)
    (by simpa only [map_zero] using (padicEmb hw).injective.ne ha)
  change ‖Algebra.norm ℚ_[p] (algebraMap ℚ_[p] (completionAt K w) a)‖ = _ at h
  rw [Algebra.norm_algebraMap, norm_pow, finrank_padic_eq_localDeg w hw] at h
  exact h.symm

local instance selectedPrime : Fact (residueChar w).Prime := ⟨residueChar_prime w⟩

local instance completionPadicAlgebra : Algebra ℚ_[residueChar w] (completionAt K w) :=
  padicAlgebra rfl
local instance completionPadicFinite : Module.Finite ℚ_[residueChar w] (completionAt K w) :=
  finite_padicAlgebra rfl

local instance completionCharZero : CharZero (completionAt K w) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective

local instance completionNontrivialNorm : NontriviallyNormedField (completionAt K w) where
  toNormedField := inferInstance
  non_trivial := by
    refine ⟨(residueChar w : completionAt K w)⁻¹, ?_⟩
    have hp0 : (residueChar w : completionAt K w) ≠ 0 :=
      Nat.cast_ne_zero.mpr (residueChar_prime w).ne_zero
    rw [norm_inv]
    apply (one_lt_inv₀ (norm_pos_iff.mpr hp0)).mpr
    have hcast : ((residueChar w : K) : completionAt K w) =
        (residueChar w : completionAt K w) :=
      map_natCast (FinitePlace.embedding w.maximalIdeal) _
    simpa only [hcast] using norm_natCast_prime_lt_one (w := w) rfl

local instance completionComplete : CompleteSpace (completionAt K w) := inferInstance
local instance completionUltrametric : IsUltrametricDist (completionAt K w) := inferInstance

abbrev AlgebraicCompletion := CompletedAlgebraicClosure.Algebraic (completionAt K w)

local instance algebraicPadicAlgebra : Algebra ℚ_[residueChar w] (AlgebraicCompletion w) :=
  ((algebraMap (completionAt K w) (AlgebraicCompletion w)).comp (padicEmb (w := w) rfl)).toAlgebra

local instance algebraicPadicTower :
    IsScalarTower ℚ_[residueChar w] (completionAt K w) (AlgebraicCompletion w) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

local instance algebraicOverPadic : Algebra.IsAlgebraic ℚ_[residueChar w] (AlgebraicCompletion w) :=
  Algebra.IsAlgebraic.trans ℚ_[residueChar w] (completionAt K w) (AlgebraicCompletion w)

theorem norm_algebraicPadicMap_eq_pow (a : ℚ_[residueChar w]) :
    ‖algebraMap ℚ_[residueChar w] (AlgebraicCompletion w) a‖ = ‖a‖ ^ localDeg w := by
  rw [IsScalarTower.algebraMap_apply ℚ_[residueChar w] (completionAt K w), norm_algebraMap']
  exact norm_padicEmb_eq_pow w rfl a

/-- The raw coefficient norm calibrated by the actual local degree. -/
def algebraicPadicNorm : MulAlgebraNorm ℚ_[residueChar w] (AlgebraicCompletion w) where
  toFun x := ‖x‖ ^ (localDeg w : ℝ)⁻¹
  map_zero' := by
    rw [norm_zero, Real.zero_rpow (inv_ne_zero (Nat.cast_ne_zero.mpr (localDeg_pos w).ne'))]
  map_one' := by rw [norm_one, Real.one_rpow]
  map_mul' x y := by
    rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  neg' x := by rw [norm_neg]
  add_le' x y := by
    have hc : 0 ≤ (localDeg w : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    calc
      ‖x + y‖ ^ (localDeg w : ℝ)⁻¹ ≤ (max ‖x‖ ‖y‖) ^ (localDeg w : ℝ)⁻¹ :=
        Real.rpow_le_rpow (norm_nonneg _) (IsUltrametricDist.norm_add_le_max x y) hc
      _ = max (‖x‖ ^ (localDeg w : ℝ)⁻¹) (‖y‖ ^ (localDeg w : ℝ)⁻¹) :=
        PositivePowerCalibration.rpow_max _ _ _ (norm_nonneg _) (norm_nonneg _) hc
      _ ≤ ‖x‖ ^ (localDeg w : ℝ)⁻¹ + ‖y‖ ^ (localDeg w : ℝ)⁻¹ :=
        max_le (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
          (le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _))
  eq_zero_of_map_eq_zero' x hx :=
    norm_eq_zero.mp ((Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg x)).mp hx).1
  smul' a x := by
    change ‖algebraMap ℚ_[residueChar w] (AlgebraicCompletion w) a * x‖ ^ (localDeg w : ℝ)⁻¹ = _
    rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
      norm_algebraicPadicMap_eq_pow w,
      Real.pow_rpow_inv_natCast (norm_nonneg a) (localDeg_pos w).ne']

theorem algebraicPadicNorm_apply (x : AlgebraicCompletion w) :
    algebraicPadicNorm w x = ‖x‖ ^ (localDeg w : ℝ)⁻¹ := rfl

theorem algebraicPadicNorm_eq_spectral :
    (algebraicPadicNorm w).toAlgebraNorm = spectralAlgNorm ℚ_[residueChar w] (AlgebraicCompletion w) :=
  spectralNorm_unique (MulRingNorm.isPowMul (algebraicPadicNorm w).toMulRingNorm)

theorem algebraic_spectralNorm_pow_eq_norm (x : AlgebraicCompletion w) :
    spectralNorm ℚ_[residueChar w] (AlgebraicCompletion w) x ^ localDeg w = ‖x‖ := by
  have h := congrArg (fun f : AlgebraNorm ℚ_[residueChar w] (AlgebraicCompletion w) => f x)
    (algebraicPadicNorm_eq_spectral w)
  change ‖x‖ ^ (localDeg w : ℝ)⁻¹ = spectralNorm ℚ_[residueChar w] (AlgebraicCompletion w) x at h
  rw [← h]
  exact Real.rpow_inv_natCast_pow (norm_nonneg x) (localDeg_pos w).ne'

local instance algebraicIsAlgClosure :
    IsAlgClosure ℚ_[residueChar w] (AlgebraicCompletion w) :=
  ⟨inferInstance, inferInstance⟩

/-- An algebraic-closure comparison constructed from the actual local field. -/
def padicAlgClEquiv :
    AlgebraicCompletion w ≃ₐ[ℚ_[residueChar w]] PadicAlgCl (residueChar w) :=
  IsAlgClosure.equiv _ _ _

theorem spectralNorm_padicAlgClEquiv (x : AlgebraicCompletion w) :
    spectralNorm ℚ_[residueChar w] (PadicAlgCl (residueChar w)) (padicAlgClEquiv w x) =
      spectralNorm ℚ_[residueChar w] (AlgebraicCompletion w) x := by
  simp only [spectralNorm, minpoly.algEquiv_eq]

theorem padicAlgClEquiv_norm_pow (x : AlgebraicCompletion w) :
    ‖padicAlgClEquiv w x‖ ^ localDeg w = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm_padicAlgClEquiv]
  exact algebraic_spectralNorm_pow_eq_norm w x

theorem padicAlgClEquiv_uniformContinuous : UniformContinuous (padicAlgClEquiv w) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  refine ⟨ε ^ localDeg w, pow_pos hε _, ?_⟩
  intro x y hxy
  rw [dist_eq_norm, ← map_sub]
  apply lt_of_pow_lt_pow_left₀ (localDeg w) hε.le
  rw [padicAlgClEquiv_norm_pow]
  simpa only [dist_eq_norm] using hxy

theorem padicAlgClEquiv_symm_uniformContinuous :
    UniformContinuous (padicAlgClEquiv w).symm := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  refine ⟨ε ^ (localDeg w : ℝ)⁻¹, Real.rpow_pos_of_pos hε _, ?_⟩
  intro x y hxy
  have hxy' : ‖x - y‖ < ε ^ (localDeg w : ℝ)⁻¹ := by
    simpa only [dist_eq_norm] using hxy
  rw [dist_eq_norm, ← map_sub]
  have h := padicAlgClEquiv_norm_pow w ((padicAlgClEquiv w).symm (x - y))
  rw [AlgEquiv.apply_symm_apply] at h
  rw [← h]
  calc
    ‖x - y‖ ^ localDeg w < (ε ^ (localDeg w : ℝ)⁻¹) ^ localDeg w :=
      pow_lt_pow_left₀ hxy' (norm_nonneg _) (localDeg_pos w).ne'
    _ = ε := Real.rpow_inv_natCast_pow hε.le (localDeg_pos w).ne'

/-- The actual completed algebraic closure compared with standard C_p. -/
def completedPadicEquiv :
    CompletedAlgebraicClosure.Field (completionAt K w) ≃+* PadicComplex (residueChar w) :=
  UniformSpace.Completion.mapRingEquiv (padicAlgClEquiv w).toRingEquiv
    (padicAlgClEquiv_uniformContinuous w).continuous
    (padicAlgClEquiv_symm_uniformContinuous w).continuous

theorem completedPadicEquiv_coe (a : AlgebraicCompletion w) :
    completedPadicEquiv w a = (padicAlgClEquiv w a : PadicComplex (residueChar w)) := by
  exact UniformSpace.Completion.mapRingHom_coe
    (padicAlgClEquiv_uniformContinuous w).continuous a

theorem completedPadicEquiv_uniformContinuous : UniformContinuous (completedPadicEquiv w) := by
  change UniformContinuous (UniformSpace.Completion.map (padicAlgClEquiv w))
  exact UniformSpace.Completion.uniformContinuous_map

theorem completedPadicEquiv_symm_uniformContinuous :
    UniformContinuous (completedPadicEquiv w).symm := by
  change UniformContinuous (UniformSpace.Completion.map (padicAlgClEquiv w).symm)
  exact UniformSpace.Completion.uniformContinuous_map

theorem completedPadicEquiv_norm_coe (a : AlgebraicCompletion w) :
    ‖completedPadicEquiv w a‖ = ‖padicAlgClEquiv w a‖ := by
  rw [completedPadicEquiv_coe, UniformSpace.Completion.norm_coe]

theorem completedPadicEquiv_norm_pow_coe (a : AlgebraicCompletion w) :
    ‖completedPadicEquiv w a‖ ^ localDeg w =
      ‖(a : CompletedAlgebraicClosure.Field (completionAt K w))‖ := by
  rw [completedPadicEquiv_norm_coe, UniformSpace.Completion.norm_coe]
  exact padicAlgClEquiv_norm_pow w a

theorem isClosed_completedPadicEquiv_norm_pow :
    IsClosed {x : CompletedAlgebraicClosure.Field (completionAt K w) |
      ‖completedPadicEquiv w x‖ ^ localDeg w = ‖x‖} :=
  isClosed_norm_pow_eq_norm continuous_norm continuous_norm (completedPadicEquiv w)
    (completedPadicEquiv_uniformContinuous w).continuous (localDeg w)

theorem completedPadicEquiv_norm_pow
    (x : CompletedAlgebraicClosure.Field (completionAt K w)) :
    ‖completedPadicEquiv w x‖ ^ localDeg w = ‖x‖ :=
  UniformSpace.Completion.induction_on x
    (isClosed_completedPadicEquiv_norm_pow w) (completedPadicEquiv_norm_pow_coe w)

end
end JoshiTeich.Act1Scene1.LocalCompletion
