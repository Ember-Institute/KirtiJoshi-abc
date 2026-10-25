import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitInterpolation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusCompletion

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RADIUS-INTERPOLATION
source: Joshi II `se:ff-rings`, the family of rho norms in
`pr:teichmuller-lift-A/B` and the topology of the bounded period subring.
fidelity: proves that any intermediate-radius value of an actual bounded
Witt element is bounded by the maximum of two endpoint values, using one
common numerator presentation. Extends the same bound to the complete
all-radius ring by density and continuity. Any family bracketing every
radius then detects exactly convergence in the all-radius topology.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; a countable bracketing family, metrizability,
Frechet algebra and paper B/period identities still require construction.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRadiusInterpolation

open JoshiTeich.Prologue
open InitialThetaBoundedWittExpansion
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

theorem value_le_endpoint_max (a r b : Radius) (har : a.val ≤ r.val) (hrb : r.val ≤ b.val)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaWittRhoValue.value D w r.val x ≤
      max (InitialThetaWittRhoValue.value D w a.val x)
        (InitialThetaWittRhoValue.value D w b.val x) := by
  let P := InitialThetaWittRhoValue.presentation D w x
  have he (ρ : Radius) := InitialThetaWittRhoValue.value_eq_of_presentation D w ρ.val
    ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne x P.exponent P.numerator P.relation
  rw [he a, he r, he b]
  exact WittWeightedDigitInterpolation.dividedValue_le_endpoint_max (Arithmetic.residueChar w.1)
    a.val r.val b.val a.property.1.ne' (a.property.2.trans ENNReal.one_lt_top).ne
    r.property.1.ne' (r.property.2.trans ENNReal.one_lt_top).ne
    b.property.1.ne' (b.property.2.trans ENNReal.one_lt_top).ne har hrb P.numerator P.exponent

theorem realValue_le_endpoint_max (a r b : Radius) (har : a.val ≤ r.val) (hrb : r.val ≤ b.val)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaWittRhoNorm.realValue D w r.val x ≤
      max (InitialThetaWittRhoNorm.realValue D w a.val x)
        (InitialThetaWittRhoNorm.realValue D w b.val x) := by
  have ha := InitialThetaWittRhoValue.value_lt_top D w a.val a.property.1.ne' a.property.2.le x
  have hb := InitialThetaWittRhoValue.value_lt_top D w b.val b.property.1.ne' b.property.2.le x
  have h := ENNReal.toReal_mono (max_lt ha hb).ne (value_le_endpoint_max D w a r b har hrb x)
  simpa only [InitialThetaWittRhoNorm.realValue, ENNReal.toReal_max ha.ne hb.ne] using h

theorem coordinateSeminorm_le_endpoint_max (a r b : Radius)
    (har : a.val ≤ r.val) (hrb : r.val ≤ b.val) (x : Carrier D w) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w r x ≤
      max (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w a x)
        (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w b x) := by
  refine (InitialThetaWittAllRadiusCompletion.inclusion_denseRange D w).induction_on
    (p := fun z : Carrier D w =>
      InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w r z ≤
        max (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w a z)
          (InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w b z)) x ?_ ?_
  · exact isClosed_le (InitialThetaWittAllRadiusCompletion.coordinateSeminorm_continuous D w r)
      ((InitialThetaWittAllRadiusCompletion.coordinateSeminorm_continuous D w a).max
        (InitialThetaWittAllRadiusCompletion.coordinateSeminorm_continuous D w b))
  · intro y
    simp only [InitialThetaWittAllRadiusCompletion.coordinateSeminorm_inclusion]
    exact realValue_le_endpoint_max D w a r b har hrb y

theorem tendsto_iff_bracketing_coordinates (S : Set Radius)
    (hS : ∀ r : Radius, ∃ a ∈ S, ∃ b ∈ S, a.val ≤ r.val ∧ r.val ≤ b.val)
    {ι : Type*} (l : Filter ι) (f : ι → Carrier D w) (x : Carrier D w) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ r ∈ S,
      Filter.Tendsto (fun i => InitialThetaWittAllRadiusCompletion.evaluate D w r (f i)) l
        (𝓝 (InitialThetaWittAllRadiusCompletion.evaluate D w r x)) := by
  constructor
  · intro h r hr
    exact (InitialThetaWittAllRadiusCompletion.tendsto_iff_coordinates D w l f x).mp h r
  · intro h
    apply (InitialThetaWittAllRadiusCompletion.tendsto_iff_coordinates D w l f x).mpr
    intro r
    obtain ⟨a, ha, b, hb, har, hrb⟩ := hS r
    have hna := tendsto_iff_norm_sub_tendsto_zero.mp (h a ha)
    have hnb := tendsto_iff_norm_sub_tendsto_zero.mp (h b hb)
    have hmax := hna.max hnb
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) (by simpa using hmax)
    have hi := coordinateSeminorm_le_endpoint_max D w a r b har hrb (f i - x)
    change ‖InitialThetaWittAllRadiusCompletion.evaluate D w r (f i - x)‖ ≤
      max ‖InitialThetaWittAllRadiusCompletion.evaluate D w a (f i - x)‖
        ‖InitialThetaWittAllRadiusCompletion.evaluate D w b (f i - x)‖ at hi
    simpa only [map_sub] using hi

end
end JoshiTeich.Act1Scene1.InitialThetaWittRadiusInterpolation
