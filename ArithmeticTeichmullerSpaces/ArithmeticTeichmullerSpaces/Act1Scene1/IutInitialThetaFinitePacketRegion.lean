import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFiniteFactorRegion
import Mathlib.MeasureTheory.Constructions.Pi

/-!
source-id: JT-SCENE1-INITIAL-THETA-FINITE-PACKET-REGION
source: `refer/iut/Iut/Concrete/Container.lean`, `fiberFiniteEquiv`,
`packet`, `productRegion_eq_pi`; `ThetaRegion.lean`, `thetaPilot`;
`Cor312/Procession.lean`, `Procession.standard`.
fidelity: assembles all finite-place tuples over a rational prime, with
labels 0 through j and distinguished label j. Uses the actual VBad roots
of one InitialThetaData. Proves compactness, positive finite product measure,
and finite support relative to the product of the normalizations, including
the standard procession of length (ell-1)/2. The product measure is not
identified with the paper's weighted log-volume or theta/BK locus.
Original consumer proofs; no reference source code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketRegion

open JoshiTeich.Prologue MeasureTheory
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

abbrev Fiber (p : Nat.Primes) :=
  {v : NumberField.FinitePlace ↥D.prime.torsionField // Arithmetic.residueChar v = p}

local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩

local instance fiberFinite (p : Nat.Primes) : Finite (Fiber D p) :=
  Arithmetic.fiber_finite (p : ℕ)

local instance fiberFintype (p : Nat.Primes) : Fintype (Fiber D p) := Fintype.ofFinite _

theorem fiber_nonempty (p : Nat.Primes) : Nonempty (Fiber D p) := by
  by_contra h
  have hs := Arithmetic.sum_localDeg (K := ↥D.prime.torsionField) (p : ℕ) p.property
  have he : (∑ v : Fiber D p, Arithmetic.localDeg v.1) = 0 :=
    Finset.sum_eq_zero fun v _ => (h ⟨v⟩).elim
  rw [he] at hs
  exact (Nat.ne_of_gt (Module.finrank_pos (R := ℚ) (M := ↥D.prime.torsionField))) hs.symm

abbrev Tuple (p : Nat.Primes) (j : ℕ) := Fin (j + 1) → Fiber D p

theorem tuple_nonempty (p : Nat.Primes) (j : ℕ) : Nonempty (Tuple D p j) :=
  ⟨fun _ => Classical.choice (fiber_nonempty D p)⟩

def packet (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    LocalCompletion.Packet ↥D.prime.torsionField (p : ℕ) (Fin (j + 1)) where
  place i := (c i).1
  residueChar_eq i := (c i).2

abbrev Total (p : Nat.Primes) (j : ℕ) :=
  ∀ c : Tuple D p j, (packet D p j c).Tensor

def region (p : Nat.Primes) (j : ℕ) : Set (Total D p j) :=
  Set.pi Set.univ fun c =>
    IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j

def integralRegion (p : Nat.Primes) (j : ℕ) : Set (Total D p j) :=
  Set.pi Set.univ fun c => ((packet D p j c).normalization : Set _)

theorem mem_region (p : Nat.Primes) (j : ℕ) (x : Total D p j) :
    x ∈ region D p j ↔ ∀ c, x c ∈
      IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j := by
  simp [region, Set.mem_pi]

theorem mem_integralRegion (p : Nat.Primes) (j : ℕ) (x : Total D p j) :
    x ∈ integralRegion D p j ↔ ∀ c, x c ∈ (packet D p j c).normalization := by
  simp [integralRegion, Set.mem_pi]

def witness (p : Nat.Primes) (j : ℕ) : Total D p j :=
  fun c => IutInitialThetaFiniteFactorRegion.scaleElt D (packet D p j c) (Fin.last j) j

theorem witness_mem_region (p : Nat.Primes) (j : ℕ) :
    witness D p j ∈ region D p j := by
  rw [mem_region]
  exact fun c => IutInitialThetaFiniteFactorRegion.scaleElt_mem_region D _ _ _

theorem region_nonempty (p : Nat.Primes) (j : ℕ) : (region D p j).Nonempty :=
  ⟨witness D p j, witness_mem_region D p j⟩

theorem region_isCompact (p : Nat.Primes) (j : ℕ) : IsCompact (region D p j) :=
  isCompact_univ_pi fun _ => IutInitialThetaFiniteFactorRegion.region_isCompact D _ _ _

theorem integralRegion_isCompact (p : Nat.Primes) (j : ℕ) :
    IsCompact (integralRegion D p j) :=
  isCompact_univ_pi fun c => (packet D p j c).normalization_isCompact

theorem region_subset_integralRegion (p : Nat.Primes) (j : ℕ) :
    region D p j ⊆ integralRegion D p j := by
  intro x hx
  rw [mem_integralRegion]
  exact fun c => IutInitialThetaFiniteFactorRegion.region_subset_normalization D _ _ _
    ((mem_region D p j x).mp hx c)

def productMeasure (p : Nat.Primes) (j : ℕ) : Measure (Total D p j) :=
  Measure.pi fun c => (packet D p j c).normalizationHaar

theorem productMeasure_region (p : Nat.Primes) (j : ℕ) :
    productMeasure D p j (region D p j) =
      ∏ c : Tuple D p j, (packet D p j c).normalizationHaar
        (IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j) := by
  exact Measure.pi_pi _ _

theorem productMeasure_integralRegion (p : Nat.Primes) (j : ℕ) :
    productMeasure D p j (integralRegion D p j) = 1 := by
  change Measure.pi _ (Set.pi Set.univ _) = 1
  rw [Measure.pi_pi]
  simp only [LocalCompletion.Packet.normalizationHaar_normalization, Finset.prod_const_one]

theorem productMeasure_region_le_one (p : Nat.Primes) (j : ℕ) :
    productMeasure D p j (region D p j) ≤ 1 := by
  rw [← productMeasure_integralRegion D p j]
  exact measure_mono (region_subset_integralRegion D p j)

theorem productMeasure_region_pos_lt_top (p : Nat.Primes) (j : ℕ) :
    0 < productMeasure D p j (region D p j) ∧
      productMeasure D p j (region D p j) < ⊤ := by
  constructor
  · rw [productMeasure_region]
    apply bot_lt_iff_ne_bot.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro c _
    exact (IutInitialThetaFiniteFactorRegion.region_haar_pos_lt_top D _ _ _).1.ne'
  · exact (productMeasure_region_le_one D p j).trans_lt (by simp)

theorem region_eq_integralRegion_of_not_bad (p : Nat.Primes) (j : ℕ)
    (hp : (p : ℕ) ∉ IutInitialThetaQRootFamily.badChars D) :
    region D p j = integralRegion D p j := by
  unfold region integralRegion
  congr 1
  funext c
  exact IutInitialThetaFiniteFactorRegion.region_eq_normalization_of_not_bad D _ _ _ hp

theorem badPrimes_finite :
    {p : Nat.Primes | (p : ℕ) ∈ IutInitialThetaQRootFamily.badChars D}.Finite :=
  Set.Finite.preimage (f := fun p : Nat.Primes => (p : ℕ))
    Subtype.val_injective.injOn (IutInitialThetaQRootFamily.badChars D).finite_toSet

theorem region_finite_support (j : ℕ) :
    {p : Nat.Primes | region D p j ≠ integralRegion D p j}.Finite := by
  apply (badPrimes_finite D).subset
  intro p hp
  by_contra hbad
  exact hp (region_eq_integralRegion_of_not_bad D p j hbad)

/-- The standard procession has j=i+1 and labels 0 through j. -/
abbrev Index := Fin ((D.prime.ℓ - 1) / 2)

theorem procession_length_pos : 0 < (D.prime.ℓ - 1) / 2 := by
  have h := D.prime.five_le
  omega

theorem capsule_card (i : Index D) : Fintype.card (Fin (i.val + 2)) = i.val + 2 :=
  Fintype.card_fin _

def processionRegion (i : Index D) (p : Nat.Primes) : Set (Total D p (i.val + 1)) :=
  region D p (i.val + 1)

theorem processionRegion_isCompact (i : Index D) (p : Nat.Primes) :
    IsCompact (processionRegion D i p) := region_isCompact D p _

theorem processionRegion_nonempty (i : Index D) (p : Nat.Primes) :
    (processionRegion D i p).Nonempty := region_nonempty D p _

theorem processionRegion_finite_support :
    {p : Nat.Primes | ∃ i : Index D,
      processionRegion D i p ≠ integralRegion D p (i.val + 1)}.Finite := by
  apply (badPrimes_finite D).subset
  rintro p ⟨i, hi⟩
  by_contra hbad
  exact hi (region_eq_integralRegion_of_not_bad D p _ hbad)

end
end JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketRegion
