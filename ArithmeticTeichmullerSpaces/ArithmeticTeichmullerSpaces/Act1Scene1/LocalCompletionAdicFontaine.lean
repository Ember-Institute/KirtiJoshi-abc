import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionHaarIndex
import ArithmeticTeichmullerSpaces.Prologue.Interfaces.PerfectoidBridge
import Mathlib.RingTheory.AdicCompletion.Topology

/-!
source-id: JT-SCENE1-LOCAL-COMPLETION-ADIC-FONTAINE
source: actual finite-place completion, integer ring and prime norm;
Mathlib IsAdic.isAdicComplete_iff and canonical PreTilt/Fontaine theta.
Joshi I arithmetic holomorphic structures motivates the place bridge.
fidelity: proves p-adic completeness of the actual completion integer ring
in its existing topology, supplies its actual coefficient map, and realizes
the existing Prologue algebraic place/bridge laws. These canonical maps do
not assert perfectoidness, theta surjectivity or a holomorphoid untilt identity.
Original proofs; no reference code copied.
boundary: Scene1/Derived; no change to Prologue-R5.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion

open JoshiTeich.Prologue NumberField
open scoped Topology Valued
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] (w : FinitePlace K)
local instance completionPrime : Fact (Arithmetic.residueChar w).Prime :=
  ⟨Arithmetic.residueChar_prime w⟩
local instance completionCharZero : CharZero (completionAt K w) :=
  charZero_of_injective_ringHom (FinitePlace.embedding w.maximalIdeal).injective
local instance integerCharZero : CharZero (integerRing w) :=
  (integerRing w).subtype.charZero

/-- The residue prime contracts in the actual completion. -/
theorem integerRing_prime_norm_lt_one :
    ‖(Arithmetic.residueChar w : completionAt K w)‖ < 1 := by
  have h := norm_natCast_prime_lt_one (p := Arithmetic.residueChar w) (w := w) rfl
  rwa [← FinitePlace.embedding_apply, map_natCast] at h

theorem integerRing_prime_nonunit : ¬ IsUnit (Arithmetic.residueChar w : integerRing w) := by
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  exact Valued.toNormedField.norm_lt_one_iff.mp (integerRing_prime_norm_lt_one w)

/-- Powers of the residue-prime ideal form a basis in the original integer-ring topology. -/
theorem integerRing_isAdic : IsAdic (Ideal.span {(Arithmetic.residueChar w : integerRing w)}) := by
  apply isAdic_iff.mpr
  constructor
  · intro n
    rw [Ideal.span_singleton_pow]
    apply principalIdeal_isOpen
    exact pow_ne_zero n (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w).ne_zero)
  · intro S hS
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hS
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (integerRing_prime_norm_lt_one w)
    refine ⟨n, ?_⟩
    rw [Ideal.span_singleton_pow, principalIdeal_eq_preimage_closedBall]
    intro x hx
    apply hball
    rw [Metric.mem_ball]
    change dist (x : completionAt K w) 0 < ε
    rw [dist_zero_right]
    have hx' : ‖(x : completionAt K w)‖ ≤ ‖(Arithmetic.residueChar w : completionAt K w)‖ ^ n := by
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, Subring.coe_pow, Subring.coe_natCast,
        norm_pow] using hx
    exact hx'.trans_lt hn

instance integerRing_isAdicComplete :
    IsAdicComplete (Ideal.span {(Arithmetic.residueChar w : integerRing w)}) (integerRing w) :=
  (integerRing_isAdic w).isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

instance integerRing_primeNonunitFact : Fact (¬ IsUnit (Arithmetic.residueChar w : integerRing w)) :=
  ⟨integerRing_prime_nonunit w⟩

/-- Restricts the actual completion embedding to global integers. -/
def integerCoefficientMap : 𝓞 K →+* integerRing w :=
  ((FinitePlace.embedding w.maximalIdeal).comp (algebraMap (𝓞 K) K)).codRestrict
    (integerRing w) (fun a => Valued.toNormedField.norm_le_one_iff.mp
      (FinitePlace.norm_le_one K w.maximalIdeal a))

theorem integerCoefficientMap_coe (a : 𝓞 K) :
    (integerCoefficientMap w a : completionAt K w) = FinitePlace.embedding w.maximalIdeal (a : K) := rfl

theorem integerCoefficientMap_injective : Function.Injective (integerCoefficientMap w) := by
  intro a b h
  apply Subtype.ext
  apply (FinitePlace.embedding w.maximalIdeal).injective
  exact congrArg (fun x : integerRing w => (x : completionAt K w)) h

def completionPlaceData : PerfectoidPlaceData K (integerRing w) (Arithmetic.residueChar w) where
  place := w
  data := Perfectoid.canonicalPerfectoidData

theorem completionPlaceData_laws : PerfectoidPlaceLaws (Arithmetic.residueChar w) (completionPlaceData w) :=
  ⟨Perfectoid.canonicalPerfectoidData_laws⟩

def completionBridgeData (L : AdelicThetaLinkData K) :
    PerfectoidBridgeData L (Arithmetic.residueChar w) (completionPlaceData w) where
  coefficientMap := integerCoefficientMap w

theorem completionBridgeData_laws (L : AdelicThetaLinkData K) (hw : w ∈ L.places) :
    PerfectoidBridgeLaws L (Arithmetic.residueChar w) (completionPlaceData w) (completionBridgeData w L) :=
  ⟨hw, completionPlaceData_laws w⟩

end
end JoshiTeich.Act1Scene1.LocalCompletion
