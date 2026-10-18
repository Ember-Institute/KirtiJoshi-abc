import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizedLogHull
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWitnessHullHaarProduct

/-!
source-id: JT-SCENE1-INITIAL-THETA-FINITE-NORMALIZED-LOG-HULL
source: Joshi III eq:bloch-kato-log-class, le:elem-lemma and
th:moccor-Mochizuki-form2's standard-point tensor witness.
fidelity: at every actual finite-place tuple, constructs original integral
Kummer images of principal units 1+pStar*scalars, whose normalized ordinary
logs form the tensor witness. Their principal regions, thickened factor
orbits and point-orbit hulls agree with the existing actual q-root regions.
The resulting actual adelic family and three volume levels are identified.
Original consumer proofs; no reference source code copied.
boundary: Scene1/Derived; no H1e/BK or different-untilt identification.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaFiniteNormalizedLogHull

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

def logScalars (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) : ∀ i, (packet D p j c).Factor i :=
  (packet D p j c).paperLogScalars
    (IutInitialThetaFiniteFactorRegion.scalars D (packet D p j c) (Fin.last j) j)

def integralClass (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) (i : Fin (j + 1)) :=
  (packet D p j c).paperLogIntegralClass
    (IutInitialThetaFiniteFactorRegion.scalars D (packet D p j c) (Fin.last j) j)
    (IutInitialThetaFiniteFactorRegion.scalars_norm_le_one D (packet D p j c) (Fin.last j) j) i

theorem integralClass_normalizedLog (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) (i : Fin (j + 1)) :
    (LocalPadicLog.normalizedIntegralKummerLogEquiv (p : ℕ)
      ((packet D p j c).logHull_norm_prime_lt_one i) (integralClass D p j c i) :
        (packet D p j c).Factor i) = logScalars D p j c i :=
  (packet D p j c).paperLogIntegralClass_normalizedLog _
    (IutInitialThetaFiniteFactorRegion.scalars_norm_le_one D (packet D p j c) (Fin.last j) j) i

theorem logScalars_norm (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) (i : Fin (j + 1)) :
    ‖logScalars D p j c i‖ =
      ‖IutInitialThetaFiniteFactorRegion.scalars D (packet D p j c) (Fin.last j) j i‖ :=
  (packet D p j c).paperLogScalars_norm _
    (IutInitialThetaFiniteFactorRegion.scalars_norm_le_one D (packet D p j c) (Fin.last j) j) i

theorem logScalars_ne_zero (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) (i : Fin (j + 1)) :
    logScalars D p j c i ≠ 0 :=
  (packet D p j c).paperLogScalars_ne_zero _
    (IutInitialThetaFiniteFactorRegion.scalars_ne_zero D (packet D p j c) (Fin.last j) j)
    (IutInitialThetaFiniteFactorRegion.scalars_norm_le_one D (packet D p j c) (Fin.last j) j) i

def witness (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) : (packet D p j c).Tensor :=
  (packet D p j c).pure (logScalars D p j c)

theorem witness_eq_integralLogTensor (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    witness D p j c = (packet D p j c).pure (fun i =>
      (LocalPadicLog.normalizedIntegralKummerLogEquiv (p : ℕ)
        ((packet D p j c).logHull_norm_prime_lt_one i) (integralClass D p j c i) :
          (packet D p j c).Factor i)) := by
  unfold witness
  congr 1
  funext i
  exact (integralClass_normalizedLog D p j c i).symm

theorem witness_singletonHull_eq_principal (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    ((packet D p j c).normalizationHull {witness D p j c} : Set (packet D p j c).Tensor) =
      (packet D p j c).principalRegion
        (IutInitialThetaFiniteFactorRegion.scaleElt D (packet D p j c) (Fin.last j) j) :=
  (packet D p j c).singletonHull_paperLogScalars _
    (IutInitialThetaFiniteFactorRegion.scalars_ne_zero D (packet D p j c) (Fin.last j) j)
    (IutInitialThetaFiniteFactorRegion.scalars_norm_le_one D (packet D p j c) (Fin.last j) j)

def componentPoints (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) : Set (packet D p j c).Tensor :=
  (packet D p j c).factorPointOrbit (witness D p j c)

def componentHull (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    Submodule (packet D p j c).normalization (packet D p j c).Tensor :=
  (packet D p j c).normalizationHull (componentPoints D p j c)

theorem componentHull_eq_existing (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    (componentHull D p j c : Set (packet D p j c).Tensor) =
      IutInitialThetaFinitePacketHull.componentHull D p j c := by
  have he := (packet D p j c).pointOrbitHull_paperLogScalars
    (IutInitialThetaFiniteFactorRegion.scalars D (packet D p j c) (Fin.last j) j)
    (IutInitialThetaFiniteFactorRegion.scalars_ne_zero D (packet D p j c) (Fin.last j) j)
    (IutInitialThetaFiniteFactorRegion.scalars_norm_le_one D (packet D p j c) (Fin.last j) j)
  change componentHull D p j c = IutInitialThetaFinitePointOrbitHull.componentHull D p j c at he
  exact (congrArg (fun M : Submodule (packet D p j c).normalization (packet D p j c).Tensor =>
    (M : Set (packet D p j c).Tensor)) he).trans
    (IutInitialThetaFinitePointOrbitHull.componentHull_eq_existing D p j c)

theorem thickenedOrbit_eq_source (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    (packet D p j c).factorOrbitScalarRegion (logScalars D p j c) (logScalars_ne_zero D p j c) =
      IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j :=
  (packet D p j c).factorOrbitScalarRegion_paperLogScalars _
    (IutInitialThetaFiniteFactorRegion.scalars_ne_zero D (packet D p j c) (Fin.last j) j)
    (IutInitialThetaFiniteFactorRegion.scalars_norm_le_one D (packet D p j c) (Fin.last j) j)


theorem componentHull_isCompact (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    IsCompact (componentHull D p j c : Set (packet D p j c).Tensor) := by
  rw [componentHull_eq_existing]
  exact IutInitialThetaFinitePacketHull.componentHull_isCompact D p j c

theorem componentHull_haar_pos_lt_top (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    0 < (packet D p j c).normalizationHaar (componentHull D p j c) ∧
      (packet D p j c).normalizationHaar (componentHull D p j c) < ⊤ := by
  rw [componentHull_eq_existing]
  exact IutInitialThetaFinitePacketHull.componentHull_haar_pos_lt_top D p j c

def hullFamily (j : ℕ) : IutInitialThetaAdelicHullClosure.Family D j
  | .finite p => fun c => ⟨componentHull D p j c,
      (componentHull_isCompact D p j c).isBounded, (componentHull_haar_pos_lt_top D p j c).1⟩
  | .infinite => IutInitialThetaFinitePointOrbitHull.hullPacketFamily D j .infinite

theorem hullFamily_eq_existing (j : ℕ) :
    hullFamily D j = IutInitialThetaFinitePointOrbitHull.hullPacketFamily D j := by
  funext vQ
  cases vQ with
  | finite p =>
    funext c
    apply Subtype.ext
    exact (componentHull_eq_existing D p j c).trans
      (IutInitialThetaFinitePointOrbitHull.componentHull_eq_existing D p j c).symm
  | infinite => rfl

def hullAdmissibleFamily (j : ℕ) : IutInitialThetaAdelicFamilyLogVolume.AdmissibleFamily D j :=
  ⟨hullFamily D j, by
    rw [hullFamily_eq_existing, IutInitialThetaFinitePointOrbitHull.hullPacketFamily_eq_existing]
    exact IutInitialThetaAdelicHullClosure.closure_sourceFamily_finite_support D j⟩

theorem hullAdmissibleFamily_eq_existing (j : ℕ) :
    hullAdmissibleFamily D j = IutInitialThetaFinitePointOrbitHull.hullAdmissibleFamily D j :=
  Subtype.ext (hullFamily_eq_existing D j)

theorem globalLogVolume_eq_existing (j : ℕ) :
    IutInitialThetaAdelicFamilyLogVolume.globalLogVolume D j (hullAdmissibleFamily D j) =
      IutInitialThetaAdelicPacketHull.globalLogVolume D j := by
  rw [hullAdmissibleFamily_eq_existing]
  exact IutInitialThetaFinitePointOrbitHull.globalHullLogVolume_eq_existing D j

theorem processionLogVolume_eq_existing :
    IutInitialThetaAdelicFamilyLogVolume.processionLogVolume D
      (fun i => hullAdmissibleFamily D (i.val + 1)) =
        IutInitialThetaAdelicPacketHull.processionLogVolume D := by
  simp only [hullAdmissibleFamily_eq_existing,
    IutInitialThetaFinitePointOrbitHull.processionHullLogVolume_eq_existing]


/-- Actual Haar volume of the packet built from the normalized-log orbit hulls. -/
def finitePacketVolume (j : ℕ) (p : Nat.Primes) : ℝ :=
  (IutInitialThetaAdelicPacketRegion.packetMeasure D j (.finite p)
    (IutInitialThetaAdelicHullClosure.productRegion D j (.finite p) (hullFamily D j (.finite p)))).toReal ^
      (1 / (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1))

theorem finitePacketVolume_eq_existing (j : ℕ) (p : Nat.Primes) :
    finitePacketVolume D j p = IutInitialThetaWitnessHullHaarProduct.packetVolume D j
      (IutInitialThetaAdelicWitnessHullBound.pointOrbitFamily D j) p := by
  unfold finitePacketVolume IutInitialThetaWitnessHullHaarProduct.packetVolume
  rw [hullFamily_eq_existing,
    IutInitialThetaAdelicWitnessHullBound.pointOrbit_hullFamily_eq_existing]

def finiteProcessionVolume : ℝ :=
  (∏ i : Index D, ∏ p ∈ IutInitialThetaFinitePacketLogVolume.badPrimes D,
    finitePacketVolume D (i.val + 1) p) ^ (1 / (((D.prime.ℓ - 1) / 2 : ℕ) : ℝ))

theorem finiteProcessionVolume_eq_existing :
    finiteProcessionVolume D = IutInitialThetaWitnessHullHaarProduct.finiteProcessionVolume D
      (fun i => IutInitialThetaAdelicWitnessHullBound.pointOrbitFamily D (i.val + 1)) := by
  simp only [finiteProcessionVolume, finitePacketVolume_eq_existing,
    IutInitialThetaWitnessHullHaarProduct.finiteProcessionVolume,
    IutInitialThetaWitnessHullHaarProduct.finiteVolume]

theorem selectedPaperProduct_pow_lt_finiteProcessionVolume :
    actualSelectedPaperRootNormProduct D ^ IutInitialThetaFiniteGlobalLowerBound.squareAverage D <
      finiteProcessionVolume D := by
  rw [finiteProcessionVolume_eq_existing]
  exact IutInitialThetaWitnessHullHaarProduct.selectedPaperRootProduct_pow_lt_finiteProcessionVolume D _

end
end JoshiTeich.Act1Scene1.IutInitialThetaFiniteNormalizedLogHull
