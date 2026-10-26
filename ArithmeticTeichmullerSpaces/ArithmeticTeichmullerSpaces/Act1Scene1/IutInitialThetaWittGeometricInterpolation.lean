import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricInterpolation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittDominantPresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusCompletion

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-GEOMETRIC-INTERPOLATION
source: Joshi II `se:ff-rings`, the rho norms of the completed
bounded Witt period ring before `pr:teichmuller-lift-A/B`.
fidelity: an actual dominant digit and one common denominator give the
geometric interpolation bound for the original localization norms.
Density and continuity extend that same bound to the existing common
ring. Strict intermediate radii admit positive interpolation weights.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; zero propagation and single-coordinate
faithfulness are separate consumers. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittGeometricInterpolation

open JoshiTeich.Prologue InitialThetaBoundedWittExpansion WittTeichmullerExpansion
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

abbrev Radius := InitialThetaWittRhoCompletion.Radius
abbrev Carrier := InitialThetaWittAllRadiusCompletion.Carrier D w

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem dividedTerm_le_realValue (ρ : Radius)
    (x : InitialThetaBoundedWittLocalization.Ring D w) (m : ℕ) (y : FieldWitt D w)
    (he : toAmbient D w x * (Arithmetic.residueChar w.1 : Ambient D w) ^ m =
      algebraMap (FieldWitt D w) (Ambient D w) y) (i : ℕ) :
    ‖digits (Arithmetic.residueChar w.1) y i‖ * ρ.val.toReal ^ i / ρ.val.toReal ^ m ≤
      InitialThetaWittRhoNorm.realValue D w ρ.val x := by
  have h := ENNReal.div_le_div_right
    (WittWeightedDigits.term_le_value (Arithmetic.residueChar w.1) ρ.val y i) (ρ.val ^ m)
  rw [← InitialThetaWittRhoValue.value_eq_of_presentation D w ρ.val
    ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne x m y he] at h
  have ht := InitialThetaWittRhoValue.value_lt_top D w ρ.val ρ.property.1.ne' ρ.property.2.le x
  have hh := ENNReal.toReal_mono ht.ne h
  simpa only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_pow, InitialThetaWittRhoNorm.realValue] using hh

theorem realValue_holder (a r b : Radius) (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) (huv : u + v = 1)
    (hr : r.val.toReal = a.val.toReal ^ u * b.val.toReal ^ v)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaWittRhoNorm.realValue D w r.val x ≤
      InitialThetaWittRhoNorm.realValue D w a.val x ^ u *
        InitialThetaWittRhoNorm.realValue D w b.val x ^ v := by
  by_cases hx : x = 0
  · simp only [hx,
      InitialThetaWittRhoNorm.realValue_zero D w r.val r.property.1.ne' r.property.2.le,
      InitialThetaWittRhoNorm.realValue_zero D w a.val a.property.1.ne' a.property.2.le,
      InitialThetaWittRhoNorm.realValue_zero D w b.val b.property.1.ne' b.property.2.le,
      Real.zero_rpow hu.ne', Real.zero_rpow hv.ne', zero_mul, le_refl]
  have ha0 : 0 < a.val.toReal := ENNReal.toReal_pos a.property.1.ne' (a.property.2.trans ENNReal.one_lt_top).ne
  have hr0 : 0 < r.val.toReal := ENNReal.toReal_pos r.property.1.ne' (r.property.2.trans ENNReal.one_lt_top).ne
  have hb0 : 0 < b.val.toReal := ENNReal.toReal_pos b.property.1.ne' (b.property.2.trans ENNReal.one_lt_top).ne
  obtain ⟨m, y, C, i, _, _, he, hnorm, hd, _, _⟩ :=
    InitialThetaWittDominantPresentation.exists_dominant_presentation D w r x hx
  let c := ‖digits (Arithmetic.residueChar w.1) y i‖
  let k : ℤ := (i : ℤ) - (m : ℤ)
  have hc : 0 < c := norm_pos_iff.mpr hd
  have hmain : InitialThetaWittRhoNorm.realValue D w r.val x = c * r.val.toReal ^ k := by
    rw [hnorm, mul_div_assoc, GeometricInterpolation.powerRatio_eq_zpow _ hr0]
  have hA := dividedTerm_le_realValue D w a x m y he i
  have hB := dividedTerm_le_realValue D w b x m y he i
  rw [mul_div_assoc, GeometricInterpolation.powerRatio_eq_zpow _ ha0] at hA
  rw [mul_div_assoc, GeometricInterpolation.powerRatio_eq_zpow _ hb0] at hB
  rw [hmain, GeometricInterpolation.monomial_interpolation
    a.val.toReal r.val.toReal b.val.toReal c u v k ha0 hb0 hc huv hr]
  exact mul_le_mul
    (Real.rpow_le_rpow (mul_nonneg hc.le (zpow_nonneg ha0.le k)) hA hu.le)
    (Real.rpow_le_rpow (mul_nonneg hc.le (zpow_nonneg hb0.le k)) hB hv.le)
    (Real.rpow_nonneg (mul_nonneg hc.le (zpow_nonneg hb0.le k)) _)
    (Real.rpow_nonneg (InitialThetaWittRhoNorm.realValue_nonneg D w a.val x) _)

theorem coordinate_holder (a r b : Radius) (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) (huv : u + v = 1)
    (hr : r.val.toReal = a.val.toReal ^ u * b.val.toReal ^ v) (x : Carrier D w) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w r x ≤
      InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w a x ^ u *
        InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w b x ^ v := by
  refine (InitialThetaWittAllRadiusCompletion.inclusion_denseRange D w).induction_on
    (p := fun z : Carrier D w =>
      InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w r z ≤
        InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w a z ^ u *
          InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w b z ^ v) x ?_ ?_
  · exact isClosed_le (InitialThetaWittAllRadiusCompletion.coordinateSeminorm_continuous D w r)
      (((InitialThetaWittAllRadiusCompletion.coordinateSeminorm_continuous D w a).rpow_const
        (fun _ => Or.inr hu.le)).mul
        ((InitialThetaWittAllRadiusCompletion.coordinateSeminorm_continuous D w b).rpow_const
          (fun _ => Or.inr hv.le)))
  · intro y
    simp only [InitialThetaWittAllRadiusCompletion.coordinateSeminorm_inclusion]
    exact realValue_holder D w a r b u v hu hv huv hr y

theorem exists_coordinate_holder (a r b : Radius) (har : a.val < r.val) (hrb : r.val < b.val) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧ u + v = 1 ∧ ∀ x : Carrier D w,
      InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w r x ≤
        InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w a x ^ u *
          InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w b x ^ v := by
  have hf (s : Radius) : s.val ≠ ⊤ := (s.property.2.trans ENNReal.one_lt_top).ne
  obtain ⟨u, v, hu, hv, huv, hr⟩ := GeometricInterpolation.exists_weights
    a.val.toReal r.val.toReal b.val.toReal (ENNReal.toReal_pos a.property.1.ne' (hf a))
      ((ENNReal.toReal_lt_toReal (hf a) (hf r)).mpr har)
      ((ENNReal.toReal_lt_toReal (hf r) (hf b)).mpr hrb)
  exact ⟨u, v, hu, hv, huv, coordinate_holder D w a r b u v hu hv huv hr⟩

end
end JoshiTeich.Act1Scene1.InitialThetaWittGeometricInterpolation
