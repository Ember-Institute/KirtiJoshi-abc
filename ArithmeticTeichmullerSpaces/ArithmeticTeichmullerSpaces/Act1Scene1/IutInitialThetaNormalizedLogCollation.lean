import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFiniteNormalizedLogHull

/-!
source-id: JT-SCENE1-INITIAL-THETA-NORMALIZED-LOG-COLLATION
source: Joshi III pr:general-cohomology-set-const, the normalized-log
expression, and the standard-point containment in form2.
fidelity: raw component sets need only contain the actual normalized-log
tensor and lie in normalization. Their original spans, without a raw Haar
hypothesis, have the proved finite support and quantitative volume bounds.
Accepts sets of actual integral Kummer class tuples via their normalized-log
tensor image; a concrete singleton class family consumes this construction.
boundary: Scene1/Derived; collation here is within the same completions,
not an identification of cross-holomorphoid H1e or the paper theta locus.
Original proofs; no reference source code copied.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaNormalizedLogCollation

open JoshiTeich.Prologue MeasureTheory IutInitialThetaFinitePacketRegion
open scoped BigOperators Classical Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩
local instance fiberFinite (p : Nat.Primes) : Finite (Fiber D p) := Arithmetic.fiber_finite (p : ℕ)
local instance fiberFintype (p : Nat.Primes) : Fintype (Fiber D p) := Fintype.ofFinite _
local instance factorAlgebra (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) (i : Fin (j + 1)) :
    Algebra ℚ_[(p : ℕ)] ((packet D p j c).Factor i) :=
  LocalCompletion.padicAlgebra ((packet D p j c).residueChar_eq i)
local instance factorFinite (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) (i : Fin (j + 1)) :
    Module.Finite ℚ_[(p : ℕ)] ((packet D p j c).Factor i) :=
  LocalCompletion.finite_padicAlgebra ((packet D p j c).residueChar_eq i)
local instance factorContinuousSMul (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) (i : Fin (j + 1)) :
    ContinuousSMul ℚ_[(p : ℕ)] ((packet D p j c).Factor i) :=
  continuousSMul_of_algebraMap _ _ (LocalCompletion.continuous_padicEmb ((packet D p j c).residueChar_eq i))
local instance factorCharZero (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) (i : Fin (j + 1)) :
    CharZero ((packet D p j c).Factor i) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding (c i).1.maximalIdeal).injective
local instance integralModule (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    Module ℤ_[(p : ℕ)] (packet D p j c).Tensor :=
  Module.compHom _ (algebraMap ℤ_[(p : ℕ)] ℚ_[(p : ℕ)])

abbrev RawFamily (j : ℕ) := ∀ (p : Nat.Primes) (c : Tuple D p j),
  {U : Set (packet D p j c).Tensor //
    IutInitialThetaFiniteNormalizedLogHull.witness D p j c ∈ U ∧
      U ⊆ (packet D p j c).normalization}

theorem witness_mem_normalization (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    IutInitialThetaFiniteNormalizedLogHull.witness D p j c ∈ (packet D p j c).normalization := by
  apply IutInitialThetaFiniteFactorRegion.region_subset_normalization D _ _ _
  rw [← IutInitialThetaFiniteNormalizedLogHull.thickenedOrbit_eq_source D p j c]
  exact (packet D p j c).pure_mem_factorOrbitScalarRegion _ _

theorem rootWitness_mem_normalizationHull (j : ℕ) (U : RawFamily D j)
    (p : Nat.Primes) (c : Tuple D p j) :
    IutInitialThetaFiniteFactorRegion.scaleElt D (packet D p j c) (Fin.last j) j ∈
      (packet D p j c).normalizationHull (U p c).1 := by
  have hs : ((packet D p j c).normalizationHull
      {IutInitialThetaFiniteNormalizedLogHull.witness D p j c} : Set (packet D p j c).Tensor) ⊆
        (packet D p j c).normalizationHull (U p c).1 :=
    Submodule.span_mono (Set.singleton_subset_iff.mpr (U p c).2.1)
  rw [IutInitialThetaFiniteNormalizedLogHull.witness_singletonHull_eq_principal] at hs
  exact hs ⟨1, (packet D p j c).normalization.one_mem, mul_one _⟩

/-- Adjoining the root is only an adapter: the original span is unchanged. -/
def rootAdapter (j : ℕ) (U : RawFamily D j) : IutInitialThetaAdelicWitnessHullBound.RawFamily D j :=
  fun p c => ⟨insert (IutInitialThetaFiniteFactorRegion.scaleElt D (packet D p j c) (Fin.last j) j)
    (U p c).1, Set.mem_insert _ _, Set.insert_subset_iff.mpr
      ⟨IutInitialThetaFiniteFactorRegion.region_subset_normalization D _ _ _
        (IutInitialThetaFiniteFactorRegion.scaleElt_mem_region D _ _ _), (U p c).2.2⟩⟩

theorem normalizationHull_rootAdapter (j : ℕ) (U : RawFamily D j)
    (p : Nat.Primes) (c : Tuple D p j) :
    (packet D p j c).normalizationHull ((rootAdapter D j U) p c).1 =
      (packet D p j c).normalizationHull (U p c).1 := by
  apply le_antisymm
  · apply (packet D p j c).normalizationHull_le_iff _ _ |>.mpr
    exact Set.insert_subset_iff.mpr ⟨rootWitness_mem_normalizationHull D j U p c,
      (packet D p j c).subset_normalizationHull _⟩
  · exact Submodule.span_mono (Set.subset_insert _ _)

/-- The component region remains the normalization span of the original log images. -/
def componentHull (j : ℕ) (U : RawFamily D j) (p : Nat.Primes) (c : Tuple D p j) :
    Submodule (packet D p j c).normalization (packet D p j c).Tensor :=
  (packet D p j c).normalizationHull (U p c).1

theorem componentHull_eq_adapter (j : ℕ) (U : RawFamily D j) (p : Nat.Primes) (c : Tuple D p j) :
    componentHull D j U p c = IutInitialThetaAdelicWitnessHullBound.componentHull D p j
      (rootAdapter D j U p) c := (normalizationHull_rootAdapter D j U p c).symm

theorem componentHull_isCompact (j : ℕ) (U : RawFamily D j) (p : Nat.Primes) (c : Tuple D p j) :
    IsCompact (componentHull D j U p c : Set (packet D p j c).Tensor) := by
  rw [componentHull_eq_adapter]
  exact IutInitialThetaAdelicWitnessHullBound.componentHull_isCompact D p j _ c

theorem componentHull_haar_pos_lt_top (j : ℕ) (U : RawFamily D j) (p : Nat.Primes) (c : Tuple D p j) :
    0 < (packet D p j c).normalizationHaar (componentHull D j U p c) ∧
      (packet D p j c).normalizationHaar (componentHull D j U p c) < ⊤ := by
  rw [componentHull_eq_adapter]
  exact IutInitialThetaAdelicWitnessHullBound.componentHull_haar_pos_lt_top D p j _ c

def hullFamily (j : ℕ) (U : RawFamily D j) : IutInitialThetaAdelicHullClosure.Family D j
  | .finite p => fun c => ⟨componentHull D j U p c,
      (componentHull_isCompact D j U p c).isBounded, (componentHull_haar_pos_lt_top D j U p c).1⟩
  | .infinite => IutInitialThetaAdelicHullClosure.sourceFamily D j .infinite

theorem hullFamily_eq_adapter (j : ℕ) (U : RawFamily D j) :
    hullFamily D j U = IutInitialThetaAdelicWitnessHullBound.hullFamily D j (rootAdapter D j U) := by
  funext vQ
  cases vQ with
  | finite p =>
    funext c
    apply Subtype.ext
    exact congrArg (fun M : Submodule (packet D p j c).normalization (packet D p j c).Tensor =>
      (M : Set (packet D p j c).Tensor)) (componentHull_eq_adapter D j U p c)
  | infinite => rfl

def hullAdmissibleFamily (j : ℕ) (U : RawFamily D j) :
    IutInitialThetaAdelicFamilyLogVolume.AdmissibleFamily D j :=
  ⟨hullFamily D j U, by
    rw [hullFamily_eq_adapter]
    exact (IutInitialThetaAdelicWitnessHullBound.hullAdmissibleFamily D j (rootAdapter D j U)).2⟩

theorem hullAdmissibleFamily_eq_adapter (j : ℕ) (U : RawFamily D j) :
    hullAdmissibleFamily D j U = IutInitialThetaAdelicWitnessHullBound.hullAdmissibleFamily D j
      (rootAdapter D j U) := Subtype.ext (hullFamily_eq_adapter D j U)

theorem globalLogVolume_bounds (j : ℕ) (U : RawFamily D j) :
    IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j -
        ((j ^ 2 : ℕ) : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤
      IutInitialThetaAdelicFamilyLogVolume.globalLogVolume D j (hullAdmissibleFamily D j U) ∧
    IutInitialThetaAdelicFamilyLogVolume.globalLogVolume D j (hullAdmissibleFamily D j U) ≤
      IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j := by
  rw [hullAdmissibleFamily_eq_adapter]
  exact IutInitialThetaAdelicWitnessHullBound.globalLogVolume_bounds D j _

/-- Actual product Haar and its separate procession geometric mean. -/
def finiteProcessionVolume (U : ∀ i : Index D, RawFamily D (i.val + 1)) : ℝ :=
  (∏ i : Index D, ∏ p ∈ IutInitialThetaFinitePacketLogVolume.badPrimes D,
    (IutInitialThetaAdelicPacketRegion.packetMeasure D (i.val + 1) (.finite p)
      (IutInitialThetaAdelicHullClosure.productRegion D (i.val + 1) (.finite p)
        (hullFamily D (i.val + 1) (U i) (.finite p)))).toReal ^
          (1 / (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (i.val + 2))) ^
            (1 / (((D.prime.ℓ - 1) / 2 : ℕ) : ℝ))

theorem finiteProcessionVolume_eq_adapter (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    finiteProcessionVolume D U = IutInitialThetaWitnessHullHaarProduct.finiteProcessionVolume D
      (fun i => rootAdapter D (i.val + 1) (U i)) := by
  simp only [finiteProcessionVolume, hullFamily_eq_adapter,
    IutInitialThetaWitnessHullHaarProduct.finiteProcessionVolume,
    IutInitialThetaWitnessHullHaarProduct.finiteVolume,
    IutInitialThetaWitnessHullHaarProduct.packetVolume, Nat.add_assoc]

theorem finiteProcessionVolume_bounds (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    0 < finiteProcessionVolume D U ∧ finiteProcessionVolume D U ≤ 1 ∧
      actualSelectedPaperRootNormProduct D ^ IutInitialThetaFiniteGlobalLowerBound.squareAverage D <
        finiteProcessionVolume D U := by
  rw [finiteProcessionVolume_eq_adapter]
  exact ⟨IutInitialThetaWitnessHullHaarProduct.finiteProcessionVolume_pos D _,
    IutInitialThetaWitnessHullHaarProduct.finiteProcessionVolume_le_one D _,
    IutInitialThetaWitnessHullHaarProduct.selectedPaperRootProduct_pow_lt_finiteProcessionVolume D _⟩

set_option maxHeartbeats 1000000

/-- Tuples of genuine original integral coefficient-image classes. -/
abbrev IntegralClassTuple (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :=
  ∀ i : Fin (j + 1), LocalPadicLog.integralKummerSubmodule
    (Ω := AlgebraicClosure ((packet D p j c).Factor i)) (p : ℕ)
      ((packet D p j c).logHull_norm_prime_lt_one i)

def classLogScalar (p : Nat.Primes) (j : ℕ) (c : Tuple D p j)
    (x : IntegralClassTuple D p j c) (i : Fin (j + 1)) : (packet D p j c).Factor i :=
  LocalPadicLog.normalizedIntegralKummerLogEquiv (p : ℕ)
    ((packet D p j c).logHull_norm_prime_lt_one i) (x i)

def classLogTensor (p : Nat.Primes) (j : ℕ) (c : Tuple D p j)
    (x : IntegralClassTuple D p j c) : (packet D p j c).Tensor :=
  (packet D p j c).pure (classLogScalar D p j c x)

def standardClassTuple (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) : IntegralClassTuple D p j c :=
  IutInitialThetaFiniteNormalizedLogHull.integralClass D p j c

theorem standardClassTuple_log (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    classLogTensor D p j c (standardClassTuple D p j c) =
      IutInitialThetaFiniteNormalizedLogHull.witness D p j c :=
  (IutInitialThetaFiniteNormalizedLogHull.witness_eq_integralLogTensor D p j c).symm

/-- A set of class tuples, with the geometric integrality bound kept explicit. -/
abbrev ClassFamily (j : ℕ) := ∀ (p : Nat.Primes) (c : Tuple D p j),
  {C : Set (IntegralClassTuple D p j c) // standardClassTuple D p j c ∈ C ∧
    ∀ x ∈ C, ∀ i, ‖classLogScalar D p j c x i‖ ≤ 1}

def rawLogImage (j : ℕ) (C : ClassFamily D j) : RawFamily D j := fun p c =>
  ⟨classLogTensor D p j c '' (C p c).1,
    ⟨standardClassTuple D p j c, (C p c).2.1, standardClassTuple_log D p j c⟩,
    by
      rintro _ ⟨x, hx, rfl⟩
      apply (packet D p j c).unitLattice_le_normalization
      exact (packet D p j c).pure_mem_lattice _ _ (fun i => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (C p c).2.2 x hx i)⟩


def singletonClassFamily (j : ℕ) : ClassFamily D j := fun p c =>
  ⟨{standardClassTuple D p j c}, Set.mem_singleton _, by
    intro x hx i
    have he := Set.mem_singleton_iff.mp hx
    subst x
    change ‖(LocalPadicLog.normalizedIntegralKummerLogEquiv (p : ℕ)
      ((packet D p j c).logHull_norm_prime_lt_one i)
        (IutInitialThetaFiniteNormalizedLogHull.integralClass D p j c i) : (packet D p j c).Factor i)‖ ≤ 1
    rw [IutInitialThetaFiniteNormalizedLogHull.integralClass_normalizedLog,
      IutInitialThetaFiniteNormalizedLogHull.logScalars_norm]
    exact IutInitialThetaFiniteFactorRegion.scalars_norm_le_one D (packet D p j c) (Fin.last j) j i⟩

theorem singletonClassFamily_image (j : ℕ) (p : Nat.Primes) (c : Tuple D p j) :
    (rawLogImage D j (singletonClassFamily D j) p c).1 =
      {IutInitialThetaFiniteNormalizedLogHull.witness D p j c} := by
  change classLogTensor D p j c '' {standardClassTuple D p j c} = _
  rw [Set.image_singleton, standardClassTuple_log]

/-- The standard integral class tuples produce the exact single-witness baseline hull. -/
theorem singletonClassFamily_hullFamily (j : ℕ) :
    hullFamily D j (rawLogImage D j (singletonClassFamily D j)) =
      IutInitialThetaAdelicWitnessHullBound.hullFamily D j
        (IutInitialThetaAdelicWitnessHullBound.singletonFamily D j) := by
  funext vQ
  cases vQ with
  | infinite => rfl
  | finite p =>
    funext c
    apply Subtype.ext
    change ((packet D p j c).normalizationHull
      (rawLogImage D j (singletonClassFamily D j) p c).1 : Set (packet D p j c).Tensor) = _
    rw [singletonClassFamily_image, IutInitialThetaFiniteNormalizedLogHull.witness_singletonHull_eq_principal]
    exact (IutInitialThetaAdelicWitnessHullBound.singleton_componentHull_eq_principal D p j c).symm

def classImageVolume (C : ∀ i : Index D, ClassFamily D (i.val + 1)) : ℝ :=
  finiteProcessionVolume D (fun i => rawLogImage D (i.val + 1) (C i))

theorem classImageVolume_bounds (C : ∀ i : Index D, ClassFamily D (i.val + 1)) :
    0 < classImageVolume D C ∧ classImageVolume D C ≤ 1 ∧
      actualSelectedPaperRootNormProduct D ^ IutInitialThetaFiniteGlobalLowerBound.squareAverage D <
        classImageVolume D C := finiteProcessionVolume_bounds D _

theorem singletonClassImageVolume_eq :
    classImageVolume D (fun i => singletonClassFamily D (i.val + 1)) =
      Real.exp (-(IutInitialThetaFiniteGlobalLowerBound.squareAverage D *
        JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D))) := by
  have he : classImageVolume D (fun i => singletonClassFamily D (i.val + 1)) =
      IutInitialThetaWitnessHullHaarProduct.finiteProcessionVolume D
        (fun i => IutInitialThetaAdelicWitnessHullBound.singletonFamily D (i.val + 1)) := by
    simp only [classImageVolume, finiteProcessionVolume, singletonClassFamily_hullFamily,
      IutInitialThetaWitnessHullHaarProduct.finiteProcessionVolume,
      IutInitialThetaWitnessHullHaarProduct.finiteVolume,
      IutInitialThetaWitnessHullHaarProduct.packetVolume, Nat.add_assoc]
  rw [he]
  exact IutInitialThetaWitnessHullHaarProduct.singleton_finiteProcessionVolume_eq D

end
end JoshiTeich.Act1Scene1.IutInitialThetaNormalizedLogCollation
