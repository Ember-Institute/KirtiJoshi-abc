import ArithmeticTeichmullerSpaces.Act1Scene1.WittWeightedDigitInterpolation
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAllRadiusCompletion

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-RADIUS-INTERPOLATION
source: Joshi II `se:ff-rings`, the family of rho norms in
`pr:teichmuller-lift-A/B` and the topology of the bounded period subring.
fidelity: bounds an intermediate-radius value of the original standard
bounded Witt ring by the maximum of two endpoint values, using one common
numerator presentation. Extends the bound to the original complete
all-radius carrier by density and continuity. Any family bracketing every
radius detects exactly convergence in its existing all-radius topology.
Only p and its primality instance enter the construction.
Original proofs using the project's actual interpolation proof pattern;
no reference implementation copied.
boundary: Scene1/Derived; a countable bracketing family, metrizability,
scalar/Frobenius structures and paper B/period identities remain separate.
No actual InitialThetaData is used. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRadiusInterpolation

open scoped ENNReal Topology
noncomputable section
variable (p : ℕ) [Fact p.Prime]

abbrev Radius := PadicWittRhoCompletion.Radius
abbrev Carrier := PadicWittAllRadiusCompletion.Carrier p

theorem value_le_endpoint_max (a r b : Radius) (har : a.val ≤ r.val) (hrb : r.val ≤ b.val)
    (x : PadicBoundedWittLocalization.Ring p) :
    PadicWittRhoValue.value p r.val x ≤
      max (PadicWittRhoValue.value p a.val x)
        (PadicWittRhoValue.value p b.val x) := by
  let P := PadicWittRhoValue.presentation p x
  have he (ρ : Radius) := PadicWittRhoValue.value_eq_of_presentation p ρ.val
    ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne x P.exponent P.numerator P.relation
  rw [he a, he r, he b]
  exact WittWeightedDigitInterpolation.dividedValue_le_endpoint_max p
    a.val r.val b.val a.property.1.ne' (a.property.2.trans ENNReal.one_lt_top).ne
    r.property.1.ne' (r.property.2.trans ENNReal.one_lt_top).ne
    b.property.1.ne' (b.property.2.trans ENNReal.one_lt_top).ne har hrb P.numerator P.exponent

theorem realValue_le_endpoint_max (a r b : Radius) (har : a.val ≤ r.val) (hrb : r.val ≤ b.val)
    (x : PadicBoundedWittLocalization.Ring p) :
    PadicWittRhoNorm.realValue p r.val x ≤
      max (PadicWittRhoNorm.realValue p a.val x)
        (PadicWittRhoNorm.realValue p b.val x) := by
  have ha := PadicWittRhoValue.value_lt_top p a.val a.property.1.ne' a.property.2.le x
  have hb := PadicWittRhoValue.value_lt_top p b.val b.property.1.ne' b.property.2.le x
  have h := ENNReal.toReal_mono (max_lt ha hb).ne (value_le_endpoint_max p a r b har hrb x)
  simpa only [PadicWittRhoNorm.realValue, ENNReal.toReal_max ha.ne hb.ne] using h

theorem coordinateSeminorm_le_endpoint_max (a r b : Radius)
    (har : a.val ≤ r.val) (hrb : r.val ≤ b.val) (x : Carrier p) :
    PadicWittAllRadiusCompletion.coordinateSeminorm p r x ≤
      max (PadicWittAllRadiusCompletion.coordinateSeminorm p a x)
        (PadicWittAllRadiusCompletion.coordinateSeminorm p b x) := by
  refine (PadicWittAllRadiusCompletion.inclusion_denseRange p).induction_on
    (p := fun z : Carrier p =>
      PadicWittAllRadiusCompletion.coordinateSeminorm p r z ≤
        max (PadicWittAllRadiusCompletion.coordinateSeminorm p a z)
          (PadicWittAllRadiusCompletion.coordinateSeminorm p b z)) x ?_ ?_
  · exact isClosed_le (PadicWittAllRadiusCompletion.coordinateSeminorm_continuous p r)
      ((PadicWittAllRadiusCompletion.coordinateSeminorm_continuous p a).max
        (PadicWittAllRadiusCompletion.coordinateSeminorm_continuous p b))
  · intro y
    simp only [PadicWittAllRadiusCompletion.coordinateSeminorm_inclusion]
    exact realValue_le_endpoint_max p a r b har hrb y

theorem tendsto_iff_bracketing_coordinates (S : Set Radius)
    (hS : ∀ r : Radius, ∃ a ∈ S, ∃ b ∈ S, a.val ≤ r.val ∧ r.val ≤ b.val)
    {ι : Type*} (l : Filter ι) (f : ι → Carrier p) (x : Carrier p) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ r ∈ S,
      Filter.Tendsto (fun i => PadicWittAllRadiusCompletion.evaluate p r (f i)) l
        (𝓝 (PadicWittAllRadiusCompletion.evaluate p r x)) := by
  constructor
  · intro h r hr
    exact (PadicWittAllRadiusCompletion.tendsto_iff_coordinates p l f x).mp h r
  · intro h
    apply (PadicWittAllRadiusCompletion.tendsto_iff_coordinates p l f x).mpr
    intro r
    obtain ⟨a, ha, b, hb, har, hrb⟩ := hS r
    have hna := tendsto_iff_norm_sub_tendsto_zero.mp (h a ha)
    have hnb := tendsto_iff_norm_sub_tendsto_zero.mp (h b hb)
    have hmax := hna.max hnb
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) (by simpa using hmax)
    have hi := coordinateSeminorm_le_endpoint_max p a r b har hrb (f i - x)
    change ‖PadicWittAllRadiusCompletion.evaluate p r (f i - x)‖ ≤
      max ‖PadicWittAllRadiusCompletion.evaluate p a (f i - x)‖
        ‖PadicWittAllRadiusCompletion.evaluate p b (f i - x)‖ at hi
    simpa only [map_sub] using hi

end
end JoshiTeich.Act1Scene1.PadicWittRadiusInterpolation
