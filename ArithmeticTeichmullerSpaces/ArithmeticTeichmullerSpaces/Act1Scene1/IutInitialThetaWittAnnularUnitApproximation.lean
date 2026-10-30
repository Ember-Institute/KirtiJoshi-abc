import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAnnularFiniteCoordinateDensity
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittNegativeTruncation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRadiusInterpolation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoUltrametric

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ANNULAR-UNIT-APPROXIMATION
source: Joshi II `se:ff-rings`, annular rho norms and the integral
representative problem preceding `pr:teichmuller-lift-A`.
fidelity: extends the original endpoint interpolation bound to the
actual annular closure. Endpoint density then gives one original
bounded Witt source approximating an annular element uniformly on a
closed interval of radii. Unit bounds at the two endpoints produce
unit bounds for this source throughout that interval. Removing its
negative p-powers constructs an original nonnegative source, preserves
those unit bounds and bounds its error by max(epsilon,rho/r).
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no uniformly bounded source approximation is
an input. A fixed positive inner radius leaves the rho/r error term.
No exact integral representative or annular extension is asserted.
The original carriers, norms and Prologue R5 are retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittAnnularUnitApproximation

open JoshiTeich.Prologue InitialThetaBoundedWittExpansion
open InitialThetaWittAnnularExponential InitialThetaWittAnnularFiniteCoordinateDensity
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Radius := InitialThetaWittRhoCompletion.Radius

theorem norm_evaluate_le_endpoint_max (ρ : Radius) (s r t : AnnularRadius ρ)
    (hsr : s.val.val ≤ r.val.val) (hrt : r.val.val ≤ t.val.val) (x : Carrier D w ρ) :
    ‖evaluate D w ρ r x‖ ≤ max ‖evaluate D w ρ s x‖ ‖evaluate D w ρ t x‖ := by
  refine (sourceInclusion_denseRange D w ρ).induction_on
    (p := fun y => ‖evaluate D w ρ r y‖ ≤
      max ‖evaluate D w ρ s y‖ ‖evaluate D w ρ t y‖) x ?_ ?_
  · exact isClosed_le (evaluate_continuous D w ρ r).norm
      ((evaluate_continuous D w ρ s).norm.max (evaluate_continuous D w ρ t).norm)
  · intro y
    change ‖InitialThetaWittRhoCompletion.inclusion D w r.val y‖ ≤
      max ‖InitialThetaWittRhoCompletion.inclusion D w s.val y‖
        ‖InitialThetaWittRhoCompletion.inclusion D w t.val y‖
    simp only [InitialThetaWittRhoCompletion.inclusion_norm]
    exact InitialThetaWittRadiusInterpolation.realValue_le_endpoint_max D w s.val r.val t.val hsr hrt y

theorem exists_unit_source_approximation (ρ : Radius) (t : AnnularRadius ρ) (x : Carrier D w ρ)
    (hbase : ‖evaluate D w ρ ⟨ρ, le_rfl⟩ x‖ ≤ 1) (ht : ‖evaluate D w ρ t x‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ y : InitialThetaBoundedWittLocalization.Ring D w,
      ∀ r : AnnularRadius ρ, r.val.val ≤ t.val.val →
        ‖InitialThetaWittRhoCompletion.inclusion D w r.val y - evaluate D w ρ r x‖ < ε ∧
        InitialThetaWittRhoNorm.realValue D w r.val.val y ≤ 1 := by
  obtain ⟨y, hybase, hyt⟩ := exists_source_approximation D w ρ t x (min ε 1)
    (lt_min hε zero_lt_one)
  refine ⟨y, fun r hrt => ?_⟩
  have herr : ‖evaluate D w ρ r (sourceInclusion D w ρ y - x)‖ < min ε 1 := by
    apply (norm_evaluate_le_endpoint_max D w ρ ⟨ρ, le_rfl⟩ r t r.property hrt _).trans_lt
    simpa only [map_sub] using max_lt hybase hyt
  change ‖InitialThetaWittRhoCompletion.inclusion D w r.val y - evaluate D w ρ r x‖ < min ε 1 at herr
  have hx : ‖evaluate D w ρ r x‖ ≤ 1 :=
    (norm_evaluate_le_endpoint_max D w ρ ⟨ρ, le_rfl⟩ r t r.property hrt x).trans (max_le hbase ht)
  refine ⟨herr.trans_le (min_le_left _ _), ?_⟩
  rw [← InitialThetaWittRhoCompletion.inclusion_norm D w r.val]
  have hsum := InitialThetaWittRhoUltrametric.norm_add_le_max D w r.val
    (InitialThetaWittRhoCompletion.inclusion D w r.val y - evaluate D w ρ r x) (evaluate D w ρ r x)
  rw [sub_add_cancel] at hsum
  exact hsum.trans (max_le (herr.le.trans (min_le_right _ _)) hx)

theorem exists_nonnegative_approximation (ρ : Radius) (t : AnnularRadius ρ) (x : Carrier D w ρ)
    (hbase : ‖evaluate D w ρ ⟨ρ, le_rfl⟩ x‖ ≤ 1) (ht : ‖evaluate D w ρ t x‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a : InitialThetaBoundedWittLocalization.Ring D w, ∃ b : FieldWitt D w,
      toAmbient D w a = algebraMap (FieldWitt D w) (Ambient D w) b ∧
      ∀ r : AnnularRadius ρ, r.val.val ≤ t.val.val →
        ‖InitialThetaWittRhoCompletion.inclusion D w r.val a - evaluate D w ρ r x‖ ≤
          max ε (ρ.val.toReal / r.val.val.toReal) ∧
        InitialThetaWittRhoNorm.realValue D w r.val.val a ≤ 1 := by
  obtain ⟨y, hy⟩ := exists_unit_source_approximation D w ρ t x hbase ht ε hε
  obtain ⟨a, b, hab, ha⟩ := InitialThetaWittNegativeTruncation.exists_nonnegative_approximation D w y
  have hybase : InitialThetaWittRhoNorm.realValue D w ρ.val y ≤ 1 :=
    (hy ⟨ρ, le_rfl⟩ t.property).2
  refine ⟨a, b, hab, fun r hrt => ?_⟩
  have hrpos : 0 < r.val.val.toReal := ENNReal.toReal_pos r.val.property.1.ne'
    (r.val.property.2.trans ENNReal.one_lt_top).ne
  have hratio0 : 0 ≤ ρ.val.toReal / r.val.val.toReal :=
    div_nonneg ENNReal.toReal_nonneg hrpos.le
  have hratio1 : ρ.val.toReal / r.val.val.toReal ≤ 1 := by
    apply (div_le_one hrpos).mpr
    exact (ENNReal.toReal_le_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne
      (r.val.property.2.trans ENNReal.one_lt_top).ne).mpr r.property
  have herr : InitialThetaWittRhoNorm.realValue D w r.val.val (y - a) ≤
      ρ.val.toReal / r.val.val.toReal :=
    (ha ρ r.val r.property).trans (mul_le_of_le_one_right hratio0 hybase)
  constructor
  · have hdiff : ‖InitialThetaWittRhoCompletion.inclusion D w r.val a -
        InitialThetaWittRhoCompletion.inclusion D w r.val y‖ ≤ ρ.val.toReal / r.val.val.toReal := by
      rw [norm_sub_rev, ← map_sub, InitialThetaWittRhoCompletion.inclusion_norm]
      exact herr
    calc
      _ = ‖(InitialThetaWittRhoCompletion.inclusion D w r.val a -
            InitialThetaWittRhoCompletion.inclusion D w r.val y) +
          (InitialThetaWittRhoCompletion.inclusion D w r.val y - evaluate D w ρ r x)‖ := by
        rw [sub_add_sub_cancel]
      _ ≤ _ := InitialThetaWittRhoUltrametric.norm_add_le_max D w r.val _ _
      _ ≤ max ε (ρ.val.toReal / r.val.val.toReal) :=
        max_le (hdiff.trans (le_max_right _ _)) ((hy r hrt).1.le.trans (le_max_left _ _))
  · have hsum := InitialThetaWittRhoNorm.realValue_add_le_max D w r.val.val
      r.val.property.1.ne' r.val.property.2.le y (-(y - a))
    rw [show y + -(y - a) = a by ring,
      InitialThetaWittRhoNorm.realValue_neg D w r.val.val r.val.property.1.ne' r.val.property.2.le] at hsum
    exact hsum.trans (max_le (hy r hrt).2 (herr.trans hratio1))

end
end JoshiTeich.Act1Scene1.InitialThetaWittAnnularUnitApproximation
