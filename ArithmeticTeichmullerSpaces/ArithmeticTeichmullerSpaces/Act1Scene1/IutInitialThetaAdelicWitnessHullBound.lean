import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePointOrbitHull

/-!
source-id: JT-SCENE1-INITIAL-THETA-ADELIC-WITNESS-HULL-BOUND
source: Joshi III le:volume-lemma3 and the standard-point witness in
th:moccor-Mochizuki-form2; reference RightHandSide's images-to-hull order.
fidelity: arbitrary raw finite component sets containing the same actual
q-root point and contained in normalization. Derives compact positive-Haar
hulls and finite adelic support without a raw positive-Haar assumption.
A singleton baseline computes the exact weighted q-pilot lower bound;
point-orbit and thickened-source families are actual consumers. Infinite
components retain the existing actual radial shell, explicitly.
boundary: Scene1/Derived; squareAverage and full torsion-field weights are
retained. No paper theta/BK/representative or final 3.12 identity.
Original proofs; no reference source code copied.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaAdelicWitnessHullBound

open JoshiTeich.Prologue MeasureTheory IutInitialThetaFinitePacketRegion
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
local instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩
local instance fiberFinite (p : Nat.Primes) : Finite (Fiber D p) := Arithmetic.fiber_finite (p : ℕ)
local instance fiberFintype (p : Nat.Primes) : Fintype (Fiber D p) := Fintype.ofFinite _
local instance integralModule (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    Module ℤ_[(p : ℕ)] (packet D p j c).Tensor :=
  Module.compHom _ (algebraMap ℤ_[(p : ℕ)] ℚ_[(p : ℕ)])

abbrev RawPacketFamily (p : Nat.Primes) (j : ℕ) := ∀ c : Tuple D p j,
  {U : Set (packet D p j c).Tensor //
    IutInitialThetaFiniteFactorRegion.scaleElt D (packet D p j c) (Fin.last j) j ∈ U ∧
      U ⊆ (packet D p j c).normalization}

abbrev RawFamily (j : ℕ) := ∀ p, RawPacketFamily D p j

def componentHull (p : Nat.Primes) (j : ℕ) (U : RawPacketFamily D p j) (c : Tuple D p j) :
    Submodule (packet D p j c).normalization (packet D p j c).Tensor :=
  (packet D p j c).normalizationHull (U c).1

theorem componentHull_subset_normalization (p : Nat.Primes) (j : ℕ)
    (U : RawPacketFamily D p j) (c : Tuple D p j) :
    (componentHull D p j U c : Set (packet D p j c).Tensor) ⊆ (packet D p j c).normalization :=
  (packet D p j c).normalizationHull_subset_normalization _ (U c).2.2

theorem componentHull_isCompact (p : Nat.Primes) (j : ℕ)
    (U : RawPacketFamily D p j) (c : Tuple D p j) :
    IsCompact (componentHull D p j U c : Set (packet D p j c).Tensor) :=
  (packet D p j c).normalizationHull_isCompact_of_pure_mem _
    (IutInitialThetaFiniteFactorRegion.scalars D (packet D p j c) (Fin.last j) j)
    (IutInitialThetaFiniteFactorRegion.scalars_ne_zero D (packet D p j c) (Fin.last j) j)
    (U c).2.1 (U c).2.2

theorem componentHull_haar_pos_lt_top (p : Nat.Primes) (j : ℕ)
    (U : RawPacketFamily D p j) (c : Tuple D p j) :
    0 < (packet D p j c).normalizationHaar (componentHull D p j U c) ∧
      (packet D p j c).normalizationHaar (componentHull D p j U c) < ⊤ :=
  (packet D p j c).normalizationHull_haar_pos_lt_top_of_pure_mem _
    (IutInitialThetaFiniteFactorRegion.scalars D (packet D p j c) (Fin.last j) j)
    (IutInitialThetaFiniteFactorRegion.scalars_ne_zero D (packet D p j c) (Fin.last j) j)
    (U c).2.1 (U c).2.2

theorem componentHull_eq_normalization_of_not_bad (p : Nat.Primes) (j : ℕ)
    (U : RawPacketFamily D p j) (c : Tuple D p j)
    (hp : (p : ℕ) ∉ IutInitialThetaQRootFamily.badChars D) :
    (componentHull D p j U c : Set (packet D p j c).Tensor) = (packet D p j c).normalization := by
  apply Set.Subset.antisymm (componentHull_subset_normalization D p j U c)
  have hw : (1 : (packet D p j c).Tensor) ∈ (U c).1 :=
    (congrArg (fun a : (packet D p j c).Tensor => a ∈ (U c).1)
      (IutInitialThetaFiniteFactorRegion.scaleElt_eq_one_of_not_bad D _ _ _ hp)).mp (U c).2.1
  intro x hx
  have h := (componentHull D p j U c).smul_mem (⟨x, hx⟩ : (packet D p j c).normalization)
    ((packet D p j c).subset_normalizationHull (U c).1 hw)
  change x * 1 ∈ componentHull D p j U c at h
  change x ∈ componentHull D p j U c
  rw [mul_one] at h
  exact h

/-- Infinite components are the existing actual radial shell. -/
def hullFamily (j : ℕ) (U : RawFamily D j) : IutInitialThetaAdelicHullClosure.Family D j
  | .finite p => fun c => ⟨componentHull D p j (U p) c,
      (componentHull_isCompact D p j (U p) c).isBounded,
      (componentHull_haar_pos_lt_top D p j (U p) c).1⟩
  | .infinite => IutInitialThetaAdelicHullClosure.sourceFamily D j .infinite

theorem hullFamily_support_subset (j : ℕ) (U : RawFamily D j) :
    {vQ | hullFamily D j U vQ ≠ IutInitialThetaAdelicHullClosure.integralFamily D j vQ} ⊆
      (IutInitialThetaAdelicPacketRegion.exceptionalPlaces D : Set RationalPlace) := by
  intro vQ hv
  by_contra he
  apply hv
  cases vQ with
  | infinite => exact False.elim (he (Finset.mem_insert_self _ _))
  | finite p =>
    funext c
    apply Subtype.ext
    apply componentHull_eq_normalization_of_not_bad
    intro hp
    exact he ((IutInitialThetaAdelicPacketRegion.finite_mem_exceptionalPlaces D p).mpr
      ((IutInitialThetaFinitePacketLogVolume.mem_badPrimes D p).mpr hp))

def hullAdmissibleFamily (j : ℕ) (U : RawFamily D j) :
    IutInitialThetaAdelicFamilyLogVolume.AdmissibleFamily D j :=
  ⟨hullFamily D j U, (IutInitialThetaAdelicPacketRegion.exceptionalPlaces D).finite_toSet.subset
    (hullFamily_support_subset D j U)⟩

theorem hullFamily_mono (j : ℕ) {U V : RawFamily D j}
    (hUV : ∀ p c, (U p c).1 ⊆ (V p c).1) : hullFamily D j U ≤ hullFamily D j V := by
  intro vQ
  cases vQ with
  | infinite => exact le_refl _
  | finite p => exact fun c => Submodule.span_mono (hUV p c)

def singletonFamily (j : ℕ) : RawFamily D j := fun p c =>
  ⟨{IutInitialThetaFiniteFactorRegion.scaleElt D (packet D p j c) (Fin.last j) j},
    Set.mem_singleton _, Set.singleton_subset_iff.mpr
      (IutInitialThetaFiniteFactorRegion.region_subset_normalization D _ _ _
        (IutInitialThetaFiniteFactorRegion.scaleElt_mem_region D _ _ _))⟩

theorem singletonFamily_hull_le (j : ℕ) (U : RawFamily D j) :
    hullFamily D j (singletonFamily D j) ≤ hullFamily D j U :=
  hullFamily_mono D j (fun p c => Set.singleton_subset_iff.mpr (U p c).2.1)

theorem singleton_componentHull_eq_principal (p : Nat.Primes) (j : ℕ) (c : Tuple D p j) :
    (componentHull D p j (singletonFamily D j p) c : Set _) =
      (packet D p j c).principalRegion
        (IutInitialThetaFiniteFactorRegion.scaleElt D (packet D p j c) (Fin.last j) j) :=
  (packet D p j c).normalizationHull_singleton_eq_principalRegion _

theorem singleton_packetLogVolume_eq (p : Nat.Primes) (j : ℕ) :
    IutInitialThetaAdelicFamilyLogVolume.packetLogVolume D j (.finite p)
      (hullFamily D j (singletonFamily D j) (.finite p)) =
        -((j ^ 2 : ℕ) : ℝ) * Real.log (p : ℕ) *
          IutInitialThetaQRootFamily.vbadWeightedFiber D (p : ℕ) := by
  rw [IutInitialThetaAdelicFamilyLogVolume.finite_packetLogVolume_eq_weighted]
  change (∑ c : Tuple D p j, IutInitialThetaFinitePacketLogVolume.tupleWeight D p j c *
    IutInitialThetaFinitePacketLogVolume.componentLogVolume D p j c
      (componentHull D p j (singletonFamily D j p) c)) = _
  simp only [singleton_componentHull_eq_principal,
    IutInitialThetaFinitePacketLowerBound.componentLogVolume_principalRegion,
    IutInitialThetaFinitePacketLowerBound.normalized_root_log_eq_ordp]
  rw [← IutInitialThetaFinitePacketLowerBound.tupleWeight_order_sum D p j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem packetLogVolume_lower_bound (p : Nat.Primes) (j : ℕ) (U : RawFamily D j) :
    -((j ^ 2 : ℕ) : ℝ) * Real.log (p : ℕ) *
        IutInitialThetaQRootFamily.vbadWeightedFiber D (p : ℕ) ≤
      IutInitialThetaAdelicFamilyLogVolume.packetLogVolume D j (.finite p)
        (hullFamily D j U (.finite p)) := by
  rw [← singleton_packetLogVolume_eq D p j]
  exact IutInitialThetaAdelicFamilyLogVolume.packetLogVolume_mono D j (.finite p)
    (singletonFamily_hull_le D j U (.finite p))

theorem hullFamily_le_shell (j : ℕ) (U : RawFamily D j) :
    hullFamily D j U ≤ IutInitialThetaAdelicHullClosure.shellFamily D j := by
  intro vQ
  cases vQ with
  | infinite => exact IutInitialThetaAdelicHullClosure.sourceFamily_le_shellFamily D j .infinite
  | finite p =>
    intro c
    exact (componentHull_subset_normalization D p j (U p) c).trans
      ((packet D p j c).normalization_subset_saturatedLogShell)

theorem packetLogVolume_nonpos (p : Nat.Primes) (j : ℕ) (U : RawFamily D j) :
    IutInitialThetaAdelicFamilyLogVolume.packetLogVolume D j (.finite p)
      (hullFamily D j U (.finite p)) ≤ 0 := by
  rw [← IutInitialThetaAdelicFamilyLogVolume.packetLogVolume_integral D j (.finite p)]
  exact IutInitialThetaAdelicFamilyLogVolume.packetLogVolume_mono D j (.finite p)
    (fun c => componentHull_subset_normalization D p j (U p) c)

theorem globalLogVolume_eq_finite_add_arch (j : ℕ) (U : RawFamily D j) :
    IutInitialThetaAdelicFamilyLogVolume.globalLogVolume D j (hullAdmissibleFamily D j U) =
      (∑ p ∈ IutInitialThetaFinitePacketLogVolume.badPrimes D,
        IutInitialThetaAdelicFamilyLogVolume.packetLogVolume D j (.finite p)
          (hullFamily D j U (.finite p))) + IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j := by
  have hs : Function.support (fun vQ => IutInitialThetaAdelicFamilyLogVolume.packetLogVolume D j vQ
      (hullFamily D j U vQ)) ⊆ (IutInitialThetaAdelicPacketRegion.exceptionalPlaces D : Set RationalPlace) :=
    (IutInitialThetaAdelicFamilyLogVolume.packetLogVolume_support_subset D j
      (hullAdmissibleFamily D j U)).trans (hullFamily_support_subset D j U)
  unfold IutInitialThetaAdelicFamilyLogVolume.globalLogVolume hullAdmissibleFamily
  rw [finsum_eq_sum_of_support_subset _ hs, IutInitialThetaAdelicPacketRegion.exceptionalPlaces,
    Finset.sum_insert (by simp), Finset.sum_image]
  · have ha : IutInitialThetaAdelicFamilyLogVolume.packetLogVolume D j .infinite
        (hullFamily D j U .infinite) = IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j :=
      IutInitialThetaAdelicFamilyLogVolume.packetLogVolume_source D j .infinite
    rw [ha, add_comm]
  · intro p _ q _ h
    exact RationalPlace.finite.inj h

theorem singleton_globalLogVolume_eq (j : ℕ) :
    IutInitialThetaAdelicFamilyLogVolume.globalLogVolume D j
      (hullAdmissibleFamily D j (singletonFamily D j)) =
        IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j -
          ((j ^ 2 : ℕ) : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
            (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  rw [globalLogVolume_eq_finite_add_arch]
  simp only [singleton_packetLogVolume_eq, mul_assoc]
  rw [← Finset.mul_sum, IutInitialThetaFiniteGlobalLowerBound.badPrimes_weighted_logSum_eq_absLogQ]
  ring

theorem globalLogVolume_bounds (j : ℕ) (U : RawFamily D j) :
    IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j -
        ((j ^ 2 : ℕ) : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤
      IutInitialThetaAdelicFamilyLogVolume.globalLogVolume D j (hullAdmissibleFamily D j U) ∧
    IutInitialThetaAdelicFamilyLogVolume.globalLogVolume D j (hullAdmissibleFamily D j U) ≤
      IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j := by
  constructor
  · rw [← singleton_globalLogVolume_eq D j]
    exact IutInitialThetaAdelicFamilyLogVolume.globalLogVolume_mono D j (singletonFamily_hull_le D j U)
  · rw [globalLogVolume_eq_finite_add_arch]
    have hs := Finset.sum_nonpos (s := IutInitialThetaFinitePacketLogVolume.badPrimes D)
      (fun p _ => packetLogVolume_nonpos D p j U)
    simpa only [zero_add] using add_le_add hs
      (le_refl (IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j))

def processionLogVolume (U : ∀ i : Index D, RawFamily D (i.val + 1)) : ℝ :=
  IutInitialThetaAdelicFamilyLogVolume.processionLogVolume D
    (fun i => hullAdmissibleFamily D (i.val + 1) (U i))

theorem singleton_processionLogVolume_eq :
    processionLogVolume D (fun i => singletonFamily D (i.val + 1)) =
      IutInitialThetaArchimedeanPacketRegion.processionLogVolume D -
        IutInitialThetaFiniteGlobalLowerBound.squareAverage D *
          JoshiTeich.ReferenceIut.QPilotData.absLogQ
            (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  simp only [processionLogVolume, IutInitialThetaAdelicFamilyLogVolume.processionLogVolume,
    singleton_globalLogVolume_eq, Finset.sum_sub_distrib, sub_div,
    IutInitialThetaArchimedeanPacketRegion.processionLogVolume,
    IutInitialThetaFiniteGlobalLowerBound.squareAverage, ← Finset.sum_mul]
  ring

theorem processionLogVolume_bounds (U : ∀ i : Index D, RawFamily D (i.val + 1)) :
    IutInitialThetaArchimedeanPacketRegion.processionLogVolume D -
        IutInitialThetaFiniteGlobalLowerBound.squareAverage D *
          JoshiTeich.ReferenceIut.QPilotData.absLogQ
            (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤ processionLogVolume D U ∧
      processionLogVolume D U ≤ IutInitialThetaArchimedeanPacketRegion.processionLogVolume D := by
  constructor
  · rw [← singleton_processionLogVolume_eq D]
    exact IutInitialThetaAdelicFamilyLogVolume.processionLogVolume_mono D
      (fun i => singletonFamily_hull_le D (i.val + 1) (U i))
  · exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun i _ => (globalLogVolume_bounds D (i.val + 1) (U i)).2) (Nat.cast_nonneg _)

def pointOrbitFamily (j : ℕ) : RawFamily D j := fun p c =>
  ⟨IutInitialThetaFinitePointOrbitHull.componentPoints D p j c,
    IutInitialThetaFinitePointOrbitHull.scaleElt_mem_componentPoints D p j c,
    (IutInitialThetaFinitePointOrbitHull.componentPoints_subset_source D p j c).trans
      (IutInitialThetaFiniteFactorRegion.region_subset_normalization D _ _ _)⟩

def sourceRegionFamily (j : ℕ) : RawFamily D j := fun p c =>
  ⟨IutInitialThetaFiniteFactorRegion.region D (packet D p j c) (Fin.last j) j,
    IutInitialThetaFiniteFactorRegion.scaleElt_mem_region D _ _ _,
    IutInitialThetaFiniteFactorRegion.region_subset_normalization D _ _ _⟩

theorem pointOrbit_hullFamily_eq_existing (j : ℕ) :
    hullFamily D j (pointOrbitFamily D j) =
      IutInitialThetaFinitePointOrbitHull.hullPacketFamily D j := by
  funext vQ
  cases vQ with
  | finite p => rfl
  | infinite =>
    funext c
    apply Subtype.ext
    exact (LocalArchimedean.factorOrbit_archLogShell c).trans
      (IutInitialThetaArchimedeanPacketHull.componentHull_eq_archLogShell D j c).symm

theorem sourceRegion_hullFamily_eq_existing (j : ℕ) :
    hullFamily D j (sourceRegionFamily D j) =
      IutInitialThetaAdelicHullClosure.adelicClosure D j
        (IutInitialThetaAdelicHullClosure.sourceFamily D j) := by
  funext vQ
  cases vQ with
  | finite p =>
    funext c
    apply Subtype.ext
    exact (IutInitialThetaFinitePacketHull.componentHull_eq_normalizationHull D p j c).symm
  | infinite =>
    have he := congrFun (pointOrbit_hullFamily_eq_existing D j) .infinite
    exact he

theorem pointOrbit_processionLogVolume_eq_existing :
    processionLogVolume D (fun i => pointOrbitFamily D (i.val + 1)) =
      IutInitialThetaAdelicPacketHull.processionLogVolume D := by
  have he (j : ℕ) : hullAdmissibleFamily D j (pointOrbitFamily D j) =
      IutInitialThetaFinitePointOrbitHull.hullAdmissibleFamily D j :=
    Subtype.ext (pointOrbit_hullFamily_eq_existing D j)
  simp only [processionLogVolume, he,
    IutInitialThetaFinitePointOrbitHull.processionHullLogVolume_eq_existing]

theorem sourceRegion_processionLogVolume_eq_existing :
    processionLogVolume D (fun i => sourceRegionFamily D (i.val + 1)) =
      IutInitialThetaAdelicPacketHull.processionLogVolume D := by
  have he (j : ℕ) : hullAdmissibleFamily D j (sourceRegionFamily D j) =
      IutInitialThetaAdelicFamilyLogVolume.closureFamily D j
        (IutInitialThetaAdelicFamilyLogVolume.sourceAdmissibleFamily D j) :=
    Subtype.ext (sourceRegion_hullFamily_eq_existing D j)
  simp only [processionLogVolume, he, IutInitialThetaAdelicFamilyLogVolume.processionLogVolume_hull]

end
end JoshiTeich.Act1Scene1.IutInitialThetaAdelicWitnessHullBound
