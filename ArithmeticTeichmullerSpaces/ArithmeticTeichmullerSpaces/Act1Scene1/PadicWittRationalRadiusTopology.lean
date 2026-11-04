import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRadiusInterpolation
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Metrizable.Basic

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-RATIONAL-RADIUS-TOPOLOGY
source: Joshi II `se:ff-rings`, the family of rho norms used in
`pr:teichmuller-lift-A/B`, and the Frechet topology of the period ring.
fidelity: constructs a countable rational subfamily bracketing every
radius. Its coordinates detect convergence in the original standard
all-radius ring and define a topological embedding into a countable
product of the original fixed-radius completions. Thus the existing
topology is metrizable. Only p and its primality instance enter the ring
constructions; the rational radii themselves do not depend on p.
Original proofs using the project's actual rational-radius construction;
no reference implementation copied.
boundary: Scene1/Derived; no change of carrier, topology or uniformity.
Scalar algebra structure, multiplicative norm equality, Frobenius,
Tate-log and paper B/period/BK identities remain separate obligations.
Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRationalRadiusTopology

open scoped ENNReal Topology
noncomputable section

abbrev Radius := PadicWittRhoCompletion.Radius
abbrev RationalRadius := {q : ℚ // 0 < q ∧ q < 1}

def toRadius (q : RationalRadius) : Radius :=
  ⟨ENNReal.ofReal (q.val : ℝ),
    ENNReal.ofReal_pos.mpr (by exact_mod_cast q.property.1),
    ENNReal.ofReal_lt_one.mpr (by exact_mod_cast q.property.2)⟩

theorem rationalRadii_bracket (r : Radius) :
    ∃ a b : RationalRadius, (toRadius a).val ≤ r.val ∧ r.val ≤ (toRadius b).val := by
  have hrfin : r.val ≠ ⊤ := (r.property.2.trans ENNReal.one_lt_top).ne
  have hrpos : 0 < r.val.toReal := ENNReal.toReal_pos r.property.1.ne' hrfin
  have hrone : r.val.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hrfin ENNReal.one_ne_top).mpr r.property.2
  obtain ⟨a, ha0, har⟩ := exists_rat_btwn hrpos
  obtain ⟨b, hrb, hb1⟩ := exists_rat_btwn hrone
  have ha1 : (a : ℝ) < 1 := har.trans hrone
  have hb0 : (0 : ℝ) < b := hrpos.trans hrb
  let a' : RationalRadius := ⟨a, by exact_mod_cast ha0, by exact_mod_cast ha1⟩
  let b' : RationalRadius := ⟨b, by exact_mod_cast hb0, by exact_mod_cast hb1⟩
  refine ⟨a', b', ?_, ?_⟩
  · change ENNReal.ofReal (a : ℝ) ≤ r.val
    rw [← ENNReal.ofReal_toReal hrfin]
    exact ENNReal.ofReal_le_ofReal har.le
  · change r.val ≤ ENNReal.ofReal (b : ℝ)
    rw [← ENNReal.ofReal_toReal hrfin]
    exact ENNReal.ofReal_le_ofReal hrb.le

variable (p : ℕ) [Fact p.Prime]

abbrev Carrier := PadicWittAllRadiusCompletion.Carrier p
abbrev RationalProduct :=
  ∀ q : RationalRadius, PadicWittRhoCompletion.Completed p (toRadius q)

def rationalCoordinates : Carrier p →+* RationalProduct p :=
  RingHom.pi (fun q => PadicWittAllRadiusCompletion.evaluate p (toRadius q))

theorem rationalCoordinates_continuous : Continuous (rationalCoordinates p) :=
  continuous_pi (fun q => PadicWittAllRadiusCompletion.evaluate_continuous p (toRadius q))

theorem tendsto_iff_rational_coordinates {ι : Type*} (l : Filter ι) (f : ι → Carrier p)
    (x : Carrier p) :
    Filter.Tendsto f l (𝓝 x) ↔ ∀ q : RationalRadius,
      Filter.Tendsto (fun i => PadicWittAllRadiusCompletion.evaluate p (toRadius q) (f i)) l
        (𝓝 (PadicWittAllRadiusCompletion.evaluate p (toRadius q) x)) := by
  have hS : ∀ r : Radius, ∃ a ∈ Set.range toRadius, ∃ b ∈ Set.range toRadius,
      a.val ≤ r.val ∧ r.val ≤ b.val := by
    intro r
    obtain ⟨a, b, har, hrb⟩ := rationalRadii_bracket r
    exact ⟨toRadius a, ⟨a, rfl⟩, toRadius b, ⟨b, rfl⟩, har, hrb⟩
  rw [PadicWittRadiusInterpolation.tendsto_iff_bracketing_coordinates
    p (Set.range toRadius) hS l f x]
  constructor
  · intro h q
    exact h (toRadius q) ⟨q, rfl⟩
  · intro h r hr
    obtain ⟨q, rfl⟩ := hr
    exact h q

theorem tendsto_iff_rationalProduct {ι : Type*} (l : Filter ι) (f : ι → Carrier p)
    (x : Carrier p) :
    Filter.Tendsto f l (𝓝 x) ↔
      Filter.Tendsto (fun i => rationalCoordinates p (f i)) l
        (𝓝 (rationalCoordinates p x)) := by
  rw [tendsto_pi_nhds]
  exact tendsto_iff_rational_coordinates p l f x

theorem rationalCoordinates_isInducing : Topology.IsInducing (rationalCoordinates p) := by
  apply Topology.isInducing_iff_nhds.mpr
  intro x
  apply le_antisymm
  · exact ((rationalCoordinates_continuous p).tendsto x).le_comap
  · have h := (tendsto_iff_rationalProduct p
      (Filter.comap (rationalCoordinates p) (𝓝 (rationalCoordinates p x))) id x).mpr
      Filter.tendsto_comap
    exact Filter.tendsto_id'.mp h

theorem rationalCoordinates_isEmbedding : Topology.IsEmbedding (rationalCoordinates p) :=
  (rationalCoordinates_isInducing p).isEmbedding

theorem rationalCoordinates_injective : Function.Injective (rationalCoordinates p) :=
  (rationalCoordinates_isEmbedding p).injective

instance carrierMetrizable : TopologicalSpace.MetrizableSpace (Carrier p) :=
  (rationalCoordinates_isEmbedding p).metrizableSpace

end
end JoshiTeich.Act1Scene1.PadicWittRationalRadiusTopology
