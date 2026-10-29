import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittNegativeTruncation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenRadiusDynamics
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoUltrametric

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-COMPLETED-NONNEGATIVE-APPROXIMATION
source: Joshi II `se:ff-rings`, completion of the bounded Witt source
and integral representatives for `pr:teichmuller-lift-A/B`.
fidelity: for a full common-ring element with unit bounds at every
radius, constructs actual bounded source approximants with no negative
p-powers. They converge at any prescribed radius and have norm at most
one at any prescribed sequence of auxiliary radii. Density supplies
simultaneous three-radius approximants; the proved negative truncation
estimate removes denominators while preserving the required bounds.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; approximants are Witt vectors over the
original tilt field, not asserted integral. Coefficient recovery and
integral annular representatives remain open. Original common-ring
topology, source, norms and Prologue R5 are retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittCompletedNonnegativeApproximation

open JoshiTeich.Prologue InitialThetaBoundedWittExpansion
open InitialThetaWittAllRadiusCompletion
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem exists_nonnegative_approximation (ρ t : Radius) (x : Carrier D w)
    (hx : ∀ r : Radius, ‖evaluate D w r x‖ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : InitialThetaBoundedWittLocalization.Ring D w, ∃ b : FieldWitt D w,
      toAmbient D w a = algebraMap (FieldWitt D w) (Ambient D w) b ∧
      ‖InitialThetaWittRhoCompletion.inclusion D w ρ a - evaluate D w ρ x‖ < ε ∧
      InitialThetaWittRhoNorm.realValue D w t.val a ≤ 1 := by
  have hpos (r : Radius) : 0 < r.val.toReal := ENNReal.toReal_pos r.property.1.ne'
    (r.property.2.trans ENNReal.one_lt_top).ne
  have hmin : 0 < min t.val.toReal (min ρ.val.toReal (ε * ρ.val.toReal)) :=
    lt_min (hpos t) (lt_min (hpos ρ) (mul_pos hε (hpos ρ)))
  obtain ⟨n, hn⟩ := ((InitialThetaWittEigenRadiusDynamics.radiusOrbit_toReal_tendsto_zero D w ρ).eventually
    (gt_mem_nhds hmin)).exists
  let s := InitialThetaWittEigenRadiusDynamics.radiusOrbit D w ρ n
  have hst : s.val.toReal ≤ t.val.toReal := (lt_min_iff.mp hn).1.le
  have hsρ : s.val.toReal ≤ ρ.val.toReal := (lt_min_iff.mp (lt_min_iff.mp hn).2).1.le
  have hsε : s.val.toReal < ε * ρ.val.toReal := (lt_min_iff.mp (lt_min_iff.mp hn).2).2
  have hsle (r : Radius) (h : s.val.toReal ≤ r.val.toReal) : s.val ≤ r.val :=
    (ENNReal.toReal_le_toReal (s.property.2.trans ENNReal.one_lt_top).ne
      (r.property.2.trans ENNReal.one_lt_top).ne).mp h
  let U : Set (Carrier D w) := {z |
    ‖evaluate D w s z - evaluate D w s x‖ < 1 ∧
    ‖evaluate D w t z - evaluate D w t x‖ < 1 ∧
    ‖evaluate D w ρ z - evaluate D w ρ x‖ < ε}
  have hopen : IsOpen U :=
    (isOpen_lt ((evaluate_continuous D w s).sub continuous_const).norm continuous_const).inter
      ((isOpen_lt ((evaluate_continuous D w t).sub continuous_const).norm continuous_const).inter
        (isOpen_lt ((evaluate_continuous D w ρ).sub continuous_const).norm continuous_const))
  have hmem : x ∈ U := by
    simp only [U, Set.mem_setOf_eq, sub_self, norm_zero]
    exact ⟨zero_lt_one, zero_lt_one, hε⟩
  obtain ⟨y, hy⟩ := (inclusion_denseRange D w).exists_mem_open hopen ⟨x, hmem⟩
  change ‖InitialThetaWittRhoCompletion.inclusion D w s y - evaluate D w s x‖ < 1 ∧
    ‖InitialThetaWittRhoCompletion.inclusion D w t y - evaluate D w t x‖ < 1 ∧
    ‖InitialThetaWittRhoCompletion.inclusion D w ρ y - evaluate D w ρ x‖ < ε at hy
  have hyunit (r : Radius)
      (h : ‖InitialThetaWittRhoCompletion.inclusion D w r y - evaluate D w r x‖ < 1) :
      InitialThetaWittRhoNorm.realValue D w r.val y ≤ 1 := by
    rw [← InitialThetaWittRhoCompletion.inclusion_norm D w r]
    have hsum := InitialThetaWittRhoUltrametric.norm_add_le_max D w r
      (InitialThetaWittRhoCompletion.inclusion D w r y - evaluate D w r x) (evaluate D w r x)
    rw [sub_add_cancel] at hsum
    exact hsum.trans (max_le h.le (hx r))
  have hys := hyunit s hy.1
  have hyt := hyunit t hy.2.1
  obtain ⟨a, b, hab, ha⟩ := InitialThetaWittNegativeTruncation.exists_nonnegative_approximation D w y
  have herr (r : Radius) (h : s.val.toReal ≤ r.val.toReal) :
      InitialThetaWittRhoNorm.realValue D w r.val (y - a) ≤ s.val.toReal / r.val.toReal :=
    (ha s r (hsle r h)).trans
      (mul_le_of_le_one_right (div_nonneg (hpos s).le (hpos r).le) hys)
  have heρ : InitialThetaWittRhoNorm.realValue D w ρ.val (y - a) < ε :=
    (herr ρ hsρ).trans_lt ((div_lt_iff₀ (hpos ρ)).mpr hsε)
  have het : InitialThetaWittRhoNorm.realValue D w t.val (y - a) ≤ 1 :=
    (herr t hst).trans ((div_le_one (hpos t)).mpr hst)
  refine ⟨a, b, hab, ?_, ?_⟩
  · have hdiff : ‖InitialThetaWittRhoCompletion.inclusion D w ρ a -
        InitialThetaWittRhoCompletion.inclusion D w ρ y‖ < ε := by
      rw [norm_sub_rev, ← map_sub, InitialThetaWittRhoCompletion.inclusion_norm]
      exact heρ
    calc
      _ = ‖(InitialThetaWittRhoCompletion.inclusion D w ρ a -
            InitialThetaWittRhoCompletion.inclusion D w ρ y) +
          (InitialThetaWittRhoCompletion.inclusion D w ρ y - evaluate D w ρ x)‖ := by
        rw [sub_add_sub_cancel]
      _ ≤ _ := InitialThetaWittRhoUltrametric.norm_add_le_max D w ρ _ _
      _ < ε := max_lt hdiff hy.2.2
  · have hsum := InitialThetaWittRhoNorm.realValue_add_le_max D w t.val t.property.1.ne'
      t.property.2.le y (-(y - a))
    rw [show y + -(y - a) = a by ring,
      InitialThetaWittRhoNorm.realValue_neg D w t.val t.property.1.ne' t.property.2.le] at hsum
    exact hsum.trans (max_le hyt het)

theorem exists_nonnegative_approximating_sequence (ρ : Radius) (t : ℕ → Radius)
    (x : Carrier D w) (hx : ∀ r : Radius, ‖evaluate D w r x‖ ≤ 1) :
    ∃ a : ℕ → InitialThetaBoundedWittLocalization.Ring D w, ∃ b : ℕ → FieldWitt D w,
      (∀ n : ℕ, toAmbient D w (a n) = algebraMap (FieldWitt D w) (Ambient D w) (b n)) ∧
      (∀ n : ℕ, InitialThetaWittRhoNorm.realValue D w (t n).val (a n) ≤ 1) ∧
      Filter.Tendsto (fun n => InitialThetaWittRhoCompletion.inclusion D w ρ (a n))
        Filter.atTop (𝓝 (evaluate D w ρ x)) := by
  have h (n : ℕ) := exists_nonnegative_approximation D w ρ (t n) x hx
    ((1 / 2 : ℝ) ^ n) (pow_pos (by norm_num) n)
  choose a b hab herr hnorm using h
  refine ⟨a, b, hab, hnorm, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (herr n).le)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))

end
end JoshiTeich.Act1Scene1.InitialThetaWittCompletedNonnegativeApproximation
