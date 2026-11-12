import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaNormalizedLogCollation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFiniteHullIndeterminacy

/-!
source-id: JT-SCENE1-INITIAL-THETA-LOG-COLLATION-ORBIT
source: reference LocalConstruct/Indeterminacy's factor images and span
transport, Cor312/RightHandSide's image-hull-volume order; Joshi III
pr:general-cohomology-set-const and th:thetam-construction.
fidelity: saturates actual normalized-log raw families under the constructed
completion-factor algebra automorphisms. Proves extensivity, monotonicity,
idempotency, invariant hulls, and monotone actual Haar products. Saturating
the actual standard integral-class image recovers the existing orbit hull
and its Haar volume. No cohomology transport is defined through logarithms.
boundary: Scene1/Derived; no cross-holomorphoid H1e/BK or full Ind1--Ind3
identification. Original proofs; no reference source code copied.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaLogCollationOrbit

open JoshiTeich.Prologue MeasureTheory IutInitialThetaFinitePacketRegion
open IutInitialThetaNormalizedLogCollation IutInitialThetaFinitePacketLogShellIndeterminacy
open scoped BigOperators Classical
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
local instance integralModule (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    Module ℤ_[(p : ℕ)] (packet D p j c).Tensor :=
  Module.compHom _ (algebraMap ℤ_[(p : ℕ)] ℚ_[(p : ℕ)])

/-- The actual full factor orbit, taken before the normalization hull. -/
def saturate (j : ℕ) (U : RawFamily D j) : RawFamily D j := fun p c =>
  ⟨(packet D p j c).factorIndeterminacyOrbit (U p c).1,
    (packet D p j c).subset_factorIndeterminacyOrbit _ (U p c).2.1, by
      intro x hx
      obtain ⟨f, hf, y, hy, rfl⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨σ, rfl⟩ := hf
      exact ((packet D p j c).factorTensorAut_image_normalization σ).subset
        ⟨y, (U p c).2.2 hy, rfl⟩⟩

theorem subset_saturate (j : ℕ) (U : RawFamily D j) (p : Nat.Primes) (c : Tuple D p j) :
    (U p c).1 ⊆ (saturate D j U p c).1 :=
  (packet D p j c).subset_factorIndeterminacyOrbit _

theorem saturate_mono (j : ℕ) {U V : RawFamily D j}
    (hUV : ∀ p c, (U p c).1 ⊆ (V p c).1) (p : Nat.Primes) (c : Tuple D p j) :
    (saturate D j U p c).1 ⊆ (saturate D j V p c).1 := by
  intro x hx
  obtain ⟨f, hf, y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨f, hf, ⟨y, hUV p c hy, hxy⟩⟩

theorem saturate_idem (j : ℕ) (U : RawFamily D j) :
    saturate D j (saturate D j U) = saturate D j U := by
  funext p c
  apply Subtype.ext
  exact (packet D p j c).factorIndeterminacyOrbit_idem _

theorem saturate_component_image (j : ℕ) (U : RawFamily D j) (p : Nat.Primes)
    (σ : Automorphisms D p j) (c : Tuple D p j) :
    (packet D p j c).factorTensorAut (σ c) '' (saturate D j U p c).1 =
      (saturate D j U p c).1 :=
  (packet D p j c).factorTensorAut_image_orbit (σ c) _

theorem saturatedHull_component_image (j : ℕ) (U : RawFamily D j) (p : Nat.Primes)
    (σ : Automorphisms D p j) (c : Tuple D p j) :
    (packet D p j c).factorTensorAut (σ c) ''
      (componentHull D j (saturate D j U) p c : Set (packet D p j c).Tensor) =
        (componentHull D j (saturate D j U) p c : Set (packet D p j c).Tensor) :=
  (packet D p j c).factorTensorAut_image_orbitHull (σ c) _

theorem saturatedHull_packet_image (j : ℕ) (U : RawFamily D j) (p : Nat.Primes)
    (σ : Automorphisms D p j) :
    packetMap D p j σ '' IutInitialThetaAdelicHullClosure.productRegion D j (.finite p)
      (hullFamily D j (saturate D j U) (.finite p)) =
        IutInitialThetaAdelicHullClosure.productRegion D j (.finite p)
          (hullFamily D j (saturate D j U) (.finite p)) := by
  change packetMap D p j σ '' Set.pi Set.univ
    (fun c => (componentHull D j (saturate D j U) p c : Set _)) = _
  rw [IutInitialThetaFiniteHullIndeterminacy.packetMap_image_product]
  congr 1
  funext c
  exact saturatedHull_component_image D j U p σ c

theorem hullFamily_mono (j : ℕ) {U V : RawFamily D j}
    (hUV : ∀ p c, (U p c).1 ⊆ (V p c).1) : hullFamily D j U ≤ hullFamily D j V := by
  intro vQ
  cases vQ with
  | infinite => exact le_refl _
  | finite p => exact fun c => Submodule.span_mono (hUV p c)

theorem hullFamily_le_saturatedHull (j : ℕ) (U : RawFamily D j) :
    hullFamily D j U ≤ hullFamily D j (saturate D j U) :=
  hullFamily_mono D j (subset_saturate D j U)

theorem globalLogVolume_le_saturatedHull (j : ℕ) (U : RawFamily D j) :
    IutInitialThetaAdelicFamilyLogVolume.globalLogVolume D j (hullAdmissibleFamily D j U) ≤
      IutInitialThetaAdelicFamilyLogVolume.globalLogVolume D j
        (hullAdmissibleFamily D j (saturate D j U)) :=
  IutInitialThetaAdelicFamilyLogVolume.globalLogVolume_mono D j (hullFamily_le_saturatedHull D j U)

/-- Inclusion is used on actual product Haar before taking the two separate roots. -/
theorem finiteProcessionVolume_mono
    {U V : ∀ i : Index D, RawFamily D (i.val + 1)}
    (hUV : ∀ i p c, (U i p c).1 ⊆ (V i p c).1) :
    finiteProcessionVolume D U ≤ finiteProcessionVolume D V := by
  unfold finiteProcessionVolume
  apply Real.rpow_le_rpow (Finset.prod_nonneg fun _ _ =>
    Finset.prod_nonneg fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _) _ (by positivity)
  apply Finset.prod_le_prod
    (fun _ _ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
  intro i _
  apply Finset.prod_le_prod (fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
  intro p _
  apply Real.rpow_le_rpow ENNReal.toReal_nonneg _ (by positivity)
  apply ENNReal.toReal_mono
    (IutInitialThetaAdelicFamilyLogVolume.packetMeasure_productRegion_pos_lt_top D (i.val + 1)
      (.finite p) (hullFamily D (i.val + 1) (V i) (.finite p))).2.ne
  exact measure_mono (IutInitialThetaAdelicHullClosure.productRegion_mono D (i.val + 1)
    (.finite p) (hullFamily_mono D (i.val + 1) (hUV i) (.finite p)))

theorem finiteProcessionVolume_le_saturatedHull (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    finiteProcessionVolume D U ≤
      finiteProcessionVolume D (fun i => saturate D (i.val + 1) (U i)) :=
  finiteProcessionVolume_mono D (fun i => subset_saturate D (i.val + 1) (U i))

/-- Full factor-orbit saturation of the actual standard integral-class image. -/
def standardOrbitFamily (j : ℕ) : RawFamily D j :=
  saturate D j (rawLogImage D j (singletonClassFamily D j))

theorem standardOrbitFamily_component (j : ℕ) (p : Nat.Primes) (c : Tuple D p j) :
    (standardOrbitFamily D j p c).1 = IutInitialThetaFiniteNormalizedLogHull.componentPoints D p j c := by
  change (packet D p j c).factorIndeterminacyOrbit
    (rawLogImage D j (singletonClassFamily D j) p c).1 = _
  rw [singletonClassFamily_image]
  rfl

theorem standardOrbitFamily_hullFamily (j : ℕ) :
    hullFamily D j (standardOrbitFamily D j) = IutInitialThetaFiniteNormalizedLogHull.hullFamily D j := by
  funext vQ
  cases vQ with
  | finite p =>
    funext c
    apply Subtype.ext
    change ((packet D p j c).normalizationHull (standardOrbitFamily D j p c).1 : Set (packet D p j c).Tensor) = _
    rw [standardOrbitFamily_component]
    rfl
  | infinite =>
    exact (congrFun (IutInitialThetaAdelicWitnessHullBound.pointOrbit_hullFamily_eq_existing D j) .infinite).trans
      (congrFun (IutInitialThetaFiniteNormalizedLogHull.hullFamily_eq_existing D j) .infinite).symm

theorem standardOrbitFamily_globalLogVolume (j : ℕ) :
    IutInitialThetaAdelicFamilyLogVolume.globalLogVolume D j
      (hullAdmissibleFamily D j (standardOrbitFamily D j)) =
        IutInitialThetaAdelicPacketHull.globalLogVolume D j := by
  have he : hullAdmissibleFamily D j (standardOrbitFamily D j) =
      IutInitialThetaFiniteNormalizedLogHull.hullAdmissibleFamily D j :=
    Subtype.ext (standardOrbitFamily_hullFamily D j)
  rw [he]
  exact IutInitialThetaFiniteNormalizedLogHull.globalLogVolume_eq_existing D j

theorem standardOrbitFamily_finiteProcessionVolume :
    finiteProcessionVolume D (fun i => standardOrbitFamily D (i.val + 1)) =
      IutInitialThetaFiniteNormalizedLogHull.finiteProcessionVolume D := by
  simp only [finiteProcessionVolume, standardOrbitFamily_hullFamily,
    IutInitialThetaFiniteNormalizedLogHull.finiteProcessionVolume,
    IutInitialThetaFiniteNormalizedLogHull.finitePacketVolume, Nat.add_assoc]

theorem standardOrbitFamily_volume_bounds :
    0 < finiteProcessionVolume D (fun i => standardOrbitFamily D (i.val + 1)) ∧
      finiteProcessionVolume D (fun i => standardOrbitFamily D (i.val + 1)) ≤ 1 ∧
      actualSelectedPaperRootNormProduct D ^ IutInitialThetaFiniteGlobalLowerBound.squareAverage D <
        finiteProcessionVolume D (fun i => standardOrbitFamily D (i.val + 1)) :=
  finiteProcessionVolume_bounds D _

end
end JoshiTeich.Act1Scene1.IutInitialThetaLogCollationOrbit
