import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTiltSharp

/-!
source-id: JT-SCENE1-INITIAL-THETA-TILT-TOPOLOGY
source: Joshi Arithmetic Holomorphic Structures tilt/untilt and common value
group; Mathlib absolute-value normed fields and ultrametric valuations.
fidelity: equips the same actual tilt carrier with the norm given by its
proved valuation. Proves rank one, nondiscrete norm values and uniform
Frobenius homeomorphism. Sharp preserves the norm, not subtraction.
Completeness and a selected holomorphoid identity remain open. Original proofs.
boundary: Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTiltTopology

open JoshiTeich.Prologue
open scoped NNReal Topology
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

/-- The real absolute value is the actual tilt valuation, with no rescaling. -/
def absoluteValue : AbsoluteValue (InitialThetaTiltField.Carrier D w) ℝ where
  toFun x := InitialThetaTiltField.valuation D w x
  map_mul' x y := by exact_mod_cast map_mul (InitialThetaTiltField.valuation D w) x y
  nonneg' x := (InitialThetaTiltField.valuation D w x).property
  eq_zero' x := by
    rw [NNReal.coe_eq_zero]
    exact InitialThetaTiltField.valuation_eq_zero_iff D w x
  add_le' x y := by
    exact (NNReal.coe_le_coe.mpr ((InitialThetaTiltField.valuation D w).map_add x y)).trans
      (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

instance carrierNormedField : NormedField (InitialThetaTiltField.Carrier D w) :=
  (absoluteValue D w).toNormedField

theorem norm_eq_valuation (x : InitialThetaTiltField.Carrier D w) :
    ‖x‖ = (InitialThetaTiltField.valuation D w x : ℝ) := rfl

theorem nnnorm_eq_valuation (x : InitialThetaTiltField.Carrier D w) :
    ‖x‖₊ = InitialThetaTiltField.valuation D w x := Subtype.ext rfl

theorem norm_sharp (x : InitialThetaTiltField.Carrier D w) :
    ‖InitialThetaTiltSharp.sharp D w x‖ = ‖x‖ := InitialThetaTiltSharp.sharp_norm_real D w x

instance carrierUltrametric : IsUltrametricDist (InitialThetaTiltField.Carrier D w) := by
  apply IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
  intro x y
  change (InitialThetaTiltField.valuation D w (x + y) : ℝ) ≤ _
  exact_mod_cast (InitialThetaTiltField.valuation D w).map_add x y

instance carrierNontriviallyNormedField :
    NontriviallyNormedField (InitialThetaTiltField.Carrier D w) where
  toNormedField := carrierNormedField D w
  non_trivial := by
    obtain ⟨x, hx0, hx1⟩ := InitialThetaTiltSharp.exists_contracting D w
    refine ⟨x⁻¹, ?_⟩
    rw [norm_inv]
    apply (one_lt_inv₀ (by exact_mod_cast hx0)).mpr
    exact_mod_cast hx1

/-- The valued topology is the topology of this same actual norm. -/
instance carrierValued : Valued (InitialThetaTiltField.Carrier D w) ℝ≥0 := NormedField.toValued

theorem valued_eq_actual :
    (Valued.v : Valuation (InitialThetaTiltField.Carrier D w) ℝ≥0) =
      InitialThetaTiltField.valuation D w := by
  ext x
  exact congrArg (fun r : ℝ≥0 => (r : ℝ)) (nnnorm_eq_valuation D w x)

instance valuationRankOne : Valuation.RankOne (InitialThetaTiltField.valuation D w) := by
  rw [← valued_eq_actual]
  exact inferInstanceAs (Valuation.RankOne (NormedField.valuation (K := InitialThetaTiltField.Carrier D w)))

/-- Subtraction is compatible with Frobenius on the actual characteristic-p tilt. -/
theorem frobenius_dist (x y : InitialThetaTiltField.Carrier D w) :
    dist (frobenius (InitialThetaTiltField.Carrier D w) (Arithmetic.residueChar w.1) x)
      (frobenius (InitialThetaTiltField.Carrier D w) (Arithmetic.residueChar w.1) y) =
        dist x y ^ Arithmetic.residueChar w.1 := by
  rw [dist_eq_norm, ← map_sub, frobenius_def, norm_pow, dist_eq_norm]

theorem inverseFrobenius_dist_pow (x y : InitialThetaTiltField.Carrier D w) :
    dist ((frobeniusEquiv (InitialThetaTiltField.Carrier D w) (Arithmetic.residueChar w.1)).symm x)
      ((frobeniusEquiv (InitialThetaTiltField.Carrier D w) (Arithmetic.residueChar w.1)).symm y) ^
        Arithmetic.residueChar w.1 = dist x y := by
  rw [← frobenius_dist]
  simp only [← coe_frobeniusEquiv, RingEquiv.apply_symm_apply]

theorem frobenius_uniformContinuous : UniformContinuous
    (frobenius (InitialThetaTiltField.Carrier D w) (Arithmetic.residueChar w.1)) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro x y hxy
  rw [frobenius_dist]
  have hp := (Arithmetic.residueChar_prime w.1).pos
  have hle : dist x y ^ Arithmetic.residueChar w.1 ≤ dist x y := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    rw [hn, pow_succ]
    exact mul_le_of_le_one_left dist_nonneg
      (pow_le_one₀ dist_nonneg (lt_of_lt_of_le hxy (min_le_right _ _)).le)
  exact hle.trans_lt (lt_of_lt_of_le hxy (min_le_left _ _))

theorem inverseFrobenius_uniformContinuous : UniformContinuous
    ((frobeniusEquiv (InitialThetaTiltField.Carrier D w) (Arithmetic.residueChar w.1)).symm) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  refine ⟨ε ^ Arithmetic.residueChar w.1, pow_pos hε _, ?_⟩
  intro x y hxy
  exact lt_of_pow_lt_pow_left₀ _ hε.le
    (by rwa [inverseFrobenius_dist_pow])

def frobeniusHomeomorph : InitialThetaTiltField.Carrier D w ≃ₜ InitialThetaTiltField.Carrier D w where
  toEquiv := (frobeniusEquiv (InitialThetaTiltField.Carrier D w) (Arithmetic.residueChar w.1)).toEquiv
  continuous_toFun := (frobenius_uniformContinuous D w).continuous
  continuous_invFun := (inverseFrobenius_uniformContinuous D w).continuous

/-- There is no largest norm value strictly below one. -/
theorem exists_norm_between (x : InitialThetaTiltField.Carrier D w) (hx0 : 0 < ‖x‖) (hx1 : ‖x‖ < 1) :
    ∃ y : InitialThetaTiltField.Carrier D w, ‖x‖ < ‖y‖ ∧ ‖y‖ < 1 := by
  let y := (frobeniusEquiv (InitialThetaTiltField.Carrier D w) (Arithmetic.residueChar w.1)).symm x
  have hy : ‖y‖ ^ Arithmetic.residueChar w.1 = ‖x‖ := by
    rw [← norm_pow]
    exact congrArg norm ((frobeniusEquiv (InitialThetaTiltField.Carrier D w)
      (Arithmetic.residueChar w.1)).apply_symm_apply x)
  have hy0 : 0 < ‖y‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hx : x = 0 := by
      rw [← (frobeniusEquiv (InitialThetaTiltField.Carrier D w)
        (Arithmetic.residueChar w.1)).apply_symm_apply x]
      change y ^ Arithmetic.residueChar w.1 = 0
      rw [h, zero_pow (Arithmetic.residueChar_prime w.1).ne_zero]
    exact (norm_pos_iff.mp hx0) hx
  have hy1 : ‖y‖ < 1 :=
    (pow_lt_one_iff_of_nonneg (norm_nonneg y) (Arithmetic.residueChar_prime w.1).ne_zero).mp (hy ▸ hx1)
  exact ⟨y, hy ▸ pow_lt_self_of_lt_one₀ hy0 hy1 (Arithmetic.residueChar_prime w.1).one_lt, hy1⟩

theorem sharp_continuousAt_zero : ContinuousAt (InitialThetaTiltSharp.sharp D w) 0 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hx
  simpa only [map_zero, dist_zero_right, norm_sharp] using hx

end
end JoshiTeich.Act1Scene1.InitialThetaTiltTopology
