import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDegreeBlockTensorGrouping

/-!
source-id: JT-SCENE1-INITIAL-THETA-DEGREE-BLOCK-REGION-GROUPING
source: Joshi III `ss:weighted-vol`, `le:volume-lemma2` (3522--3545),
the actual degree-block tensor equivalence and integral tensor generators.
fidelity: proves that the original integral factor-set lattice maps to
the iterated integral span of the actual block lattices. Specializes this
identity to scalar regions and the existing ordinary-log root region.
boundary: Scene1/Derived; original Z_p scalar actions and actual factor
sets are retained. Does not infer a paper theta or weighted measure identity.
Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1.DegreeBlockRegionGrouping

open JoshiTeich.Prologue SelectedDegreeBlockVolume DegreeBlockTensorGrouping
open scoped BigOperators TensorProduct Classical
universe u
noncomputable section

theorem multilinear_mem_of_mem_spans
    {R : Type*} [CommSemiring R] {ι : Type*} [Fintype ι]
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    {N : Type*} [AddCommMonoid N] [Module R N]
    (f : MultilinearMap R M N) (S : ∀ i, Set (M i)) (U : Submodule R N)
    (hgen : ∀ x, (∀ i, x i ∈ S i) → f x ∈ U)
    (x : ∀ i, M i) (hx : ∀ i, x i ∈ Submodule.span R (S i)) : f x ∈ U := by
  classical
  have h (s : Finset ι) : ∀ x : ∀ i, M i,
      (∀ i ∈ s, x i ∈ Submodule.span R (S i)) →
      (∀ i ∉ s, x i ∈ S i) → f x ∈ U := by
    induction s using Finset.induction_on with
    | empty =>
      intro x _ hS
      exact hgen x (fun i => hS i (Finset.notMem_empty i))
    | @insert i s his ih =>
      intro x hx hS
      have hspan : Submodule.span R (S i) ≤ U.comap (f.toLinearMap x i) := by
        apply Submodule.span_le.mpr
        intro a ha
        change f (Function.update x i a) ∈ U
        apply ih
        · intro j hj
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hj his)]
          exact hx j (Finset.mem_insert_of_mem hj)
        · intro j hjs
          by_cases hji : j = i
          · subst j
            simpa only [Function.update_self] using ha
          · rw [Function.update_of_ne hji]
            exact hS j (by simp only [Finset.mem_insert]; exact not_or.mpr ⟨hji, hjs⟩)
      have hmem := hspan (hx i (Finset.mem_insert_self _ _))
      change f (Function.update x i (x i)) ∈ U at hmem
      simpa only [Function.update_eq_self] using hmem
  exact h Finset.univ x (fun i _ => hx i) (fun i hi => (hi (Finset.mem_univ i)).elim)

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) [Fact p.Prime]

local instance originalIntegralModule : Module ℤ_[p] (SelectedThetaTensor.packet D p).Tensor :=
  Module.compHom (SelectedThetaTensor.packet D p).Tensor (algebraMap ℤ_[p] ℚ_[p])

local instance blockIntegralModule (d : DegreeSupport D p) :
    Module ℤ_[p] (degreePacket D p d).Tensor :=
  Module.compHom (degreePacket D p d).Tensor (algebraMap ℤ_[p] ℚ_[p])

local instance groupedIntegralModule : Module ℤ_[p] (GroupedTensor D p) :=
  Module.compHom (GroupedTensor D p) (algebraMap ℤ_[p] ℚ_[p])

def groupingIntegral : (SelectedThetaTensor.packet D p).Tensor →ₗ[ℤ_[p]] GroupedTensor D p where
  toFun := groupingLinear D p
  map_add' := (groupingLinear D p).map_add
  map_smul' r x := (groupingLinear D p).map_smul (r : ℚ_[p]) x

def groupedIntegralPure : MultilinearMap ℤ_[p]
    (fun d : DegreeSupport D p => (degreePacket D p d).Tensor) (GroupedTensor D p) where
  toFun := PiTensorProduct.tprod ℚ_[p]
  map_update_add' m i x y := (PiTensorProduct.tprod ℚ_[p]).map_update_add m i x y
  map_update_smul' m i r x := by
    change (PiTensorProduct.tprod ℚ_[p]) (Function.update m i ((r : ℚ_[p]) • x)) =
      (r : ℚ_[p]) • (PiTensorProduct.tprod ℚ_[p]) (Function.update m i x)
    exact (PiTensorProduct.tprod ℚ_[p]).map_update_smul m i (r : ℚ_[p]) x

def groupedRegion (S : RegionFamily D p) : Submodule ℤ_[p] (GroupedTensor D p) :=
  Submodule.span ℤ_[p] {t | ∃ a : ∀ d, (degreePacket D p d).Tensor,
    (∀ d, a d ∈ S d) ∧ PiTensorProduct.tprod ℚ_[p] a = t}

def factorRegions (S : ∀ i, Set ((SelectedThetaTensor.packet D p).Factor i)) : RegionFamily D p :=
  fun d => (degreePacket D p d).lattice (fun i => S i.1)

def recombineFactors
    (a : ∀ d : DegreeSupport D p, ∀ i : DegreeFiber D p d, (degreePacket D p d).Factor i)
    (i : Index D p) : (SelectedThetaTensor.packet D p).Factor i :=
  a (blockIndexEquiv D p i).1 (blockIndexEquiv D p i).2

omit [Fact p.Prime] in
theorem recombineFactors_block
    (a : ∀ d : DegreeSupport D p, ∀ i : DegreeFiber D p d, (degreePacket D p d).Factor i)
    (d : DegreeSupport D p) (i : DegreeFiber D p d) : recombineFactors D p a i.1 = a d i := by
  rcases d with ⟨d, hd⟩
  rcases i with ⟨i, hi⟩
  change Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p i) = d at hi
  subst d
  rfl

theorem lattice_map_grouping (S : ∀ i, Set ((SelectedThetaTensor.packet D p).Factor i)) :
    ((SelectedThetaTensor.packet D p).lattice S).map (groupingIntegral D p) =
      groupedRegion D p (factorRegions D p S) := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    change groupingLinear D p ((SelectedThetaTensor.packet D p).pure a) ∈
      groupedRegion D p (factorRegions D p S)
    rw [groupingLinear_pure]
    apply Submodule.subset_span
    refine ⟨fun d => (degreePacket D p d).pure (fun i => a i.1), ?_, rfl⟩
    intro d
    exact (degreePacket D p d).pure_mem_lattice _ _ (fun i => ha i.1)
  · apply Submodule.span_le.mpr
    rintro _ ⟨b, hb, rfl⟩
    let U := ((SelectedThetaTensor.packet D p).lattice S).map (groupingIntegral D p)
    let G : ∀ d : DegreeSupport D p, Set (degreePacket D p d).Tensor :=
      fun d => {t | ∃ a : ∀ i : DegreeFiber D p d, (degreePacket D p d).Factor i,
        (∀ i, a i ∈ S i.1) ∧ (degreePacket D p d).pure a = t}
    apply multilinear_mem_of_mem_spans (groupedIntegralPure D p) G U ?_ b hb
    intro a ha
    choose z hz heq using ha
    let w := recombineFactors D p z
    have hw : ∀ i, w i ∈ S i := fun i => hz (blockIndexEquiv D p i).1 (blockIndexEquiv D p i).2
    refine Submodule.mem_map.mpr ⟨(SelectedThetaTensor.packet D p).pure w,
      (SelectedThetaTensor.packet D p).pure_mem_lattice S w hw, ?_⟩
    change groupingLinear D p ((SelectedThetaTensor.packet D p).pure w) = PiTensorProduct.tprod ℚ_[p] a
    rw [groupingLinear_pure]
    apply congrArg (PiTensorProduct.tprod ℚ_[p])
    funext d
    have hblock : (fun i : DegreeFiber D p d => w i.1) = z d := by
      funext i
      exact recombineFactors_block D p z d i
    rw [hblock]
    exact heq d

theorem groupingIntegral_injective : Function.Injective (groupingIntegral D p) := by
  intro x y h
  exact DegreeBlockTensorGrouping.groupingLinear_injective D p h

theorem groupedRegion_mem_iff
    (S : ∀ i, Set ((SelectedThetaTensor.packet D p).Factor i))
    (y : GroupedTensor D p) :
    y ∈ groupedRegion D p (factorRegions D p S) ↔
      ∃ x, x ∈ (SelectedThetaTensor.packet D p).lattice S ∧
        groupingIntegral D p x = y := by
  rw [← lattice_map_grouping D p S]
  exact Submodule.mem_map

theorem groupedRegion_preimage_unique
    (S : ∀ i, Set ((SelectedThetaTensor.packet D p).Factor i))
    {x y : (SelectedThetaTensor.packet D p).Tensor}
    (_hx : x ∈ (SelectedThetaTensor.packet D p).lattice S)
    (_hy : y ∈ (SelectedThetaTensor.packet D p).lattice S)
    (hxy : groupingIntegral D p x = groupingIntegral D p y) : x = y := by
  exact groupingIntegral_injective D p hxy

noncomputable def groupedRegion_preimage
    (S : ∀ i, Set ((SelectedThetaTensor.packet D p).Factor i))
    (y : GroupedTensor D p)
    (hy : y ∈ groupedRegion D p (factorRegions D p S)) :
    (SelectedThetaTensor.packet D p).Tensor :=
  Classical.choose (groupedRegion_mem_iff D p S y |>.mp hy)

theorem groupedRegion_preimage_mem
    (S : ∀ i, Set ((SelectedThetaTensor.packet D p).Factor i))
    (y : GroupedTensor D p)
    (hy : y ∈ groupedRegion D p (factorRegions D p S)) :
    groupedRegion_preimage D p S y hy ∈ (SelectedThetaTensor.packet D p).lattice S ∧
      groupingIntegral D p (groupedRegion_preimage D p S y hy) = y := by
  exact Classical.choose_spec (groupedRegion_mem_iff D p S y |>.mp hy)

theorem groupedRegion_preimage_eq
    (S : ∀ i, Set ((SelectedThetaTensor.packet D p).Factor i))
    (y : GroupedTensor D p)
    (hy : y ∈ groupedRegion D p (factorRegions D p S))
    {x : (SelectedThetaTensor.packet D p).Tensor}
    (_hx : x ∈ (SelectedThetaTensor.packet D p).lattice S)
    (hxy : groupingIntegral D p x = y) :
    x = groupedRegion_preimage D p S y hy := by
  apply groupingIntegral_injective D p
  exact hxy.trans (groupedRegion_preimage_mem D p S y hy).2.symm

theorem scalarLattice_map_grouping
    (z : ∀ i, (SelectedThetaTensor.packet D p).Factor i) :
    ((SelectedThetaTensor.packet D p).scalarLattice z).map (groupingIntegral D p) =
      groupedRegion D p (scalarRegions D p z) :=
  lattice_map_grouping D p _

theorem scalarGroupedRegion_mem_iff
    (z : ∀ i, (SelectedThetaTensor.packet D p).Factor i)
    (y : GroupedTensor D p) :
    y ∈ groupedRegion D p (scalarRegions D p z) ↔
      ∃ x, x ∈ (SelectedThetaTensor.packet D p).scalarLattice z ∧
        groupingIntegral D p x = y := by
  have hS : scalarRegions D p z = factorRegions D p
      (fun i => (fun x => z i * x) '' Metric.closedBall 0 1) := by
    funext d
    rfl
  have hL : (SelectedThetaTensor.packet D p).scalarLattice z =
      (SelectedThetaTensor.packet D p).lattice
        (fun i => (fun x => z i * x) '' Metric.closedBall 0 1) := by
    rfl
  rw [hS, hL]
  exact groupedRegion_mem_iff D p
    (fun i => (fun x => z i * x) '' Metric.closedBall 0 1) y

theorem logRegion_map_grouping :
    (SelectedThetaTensor.region D p).map (groupingIntegral D p) =
      groupedRegion D p (logRegions D p) :=
  scalarLattice_map_grouping D p _

theorem logRegion_mem_iff (y : GroupedTensor D p) :
    y ∈ groupedRegion D p (logRegions D p) ↔
      ∃ x, x ∈ SelectedThetaTensor.region D p ∧ groupingIntegral D p x = y := by
  have hS : logRegions D p = factorRegions D p
      (fun i => iutInitialThetaFullQRootLogBall D
        (SelectedThetaTensor.sourceAt D p i)) := by
    funext d
    rfl
  have hL : SelectedThetaTensor.region D p =
      (SelectedThetaTensor.packet D p).lattice
        (fun i => iutInitialThetaFullQRootLogBall D
          (SelectedThetaTensor.sourceAt D p i)) := by
    rfl
  rw [hS, hL]
  exact groupedRegion_mem_iff D p
    (fun i => iutInitialThetaFullQRootLogBall D
      (SelectedThetaTensor.sourceAt D p i)) y

theorem groupedRootValue_mem_groupedRegion :
    groupedRootValue D p ∈ groupedRegion D p (logRegions D p) := by
  rw [← logRegion_map_grouping D p]
  exact Submodule.mem_map.mpr ⟨SelectedThetaTensor.value D p,
    SelectedThetaTensor.value_mem_region D p, groupingEquiv_rootValue D p⟩

theorem groupedRootValue_preimage_eq_value
    (hy : groupedRootValue D p ∈ groupedRegion D p
      (factorRegions D p (fun i => iutInitialThetaFullQRootLogBall D
        (SelectedThetaTensor.sourceAt D p i)))) :
    groupedRegion_preimage D p
        (fun i => iutInitialThetaFullQRootLogBall D
          (SelectedThetaTensor.sourceAt D p i))
        (groupedRootValue D p) hy =
      SelectedThetaTensor.value D p := by
  apply (groupedRegion_preimage_eq D p
    (fun i => iutInitialThetaFullQRootLogBall D
      (SelectedThetaTensor.sourceAt D p i)) (groupedRootValue D p) hy
    (x := SelectedThetaTensor.value D p)
    (SelectedThetaTensor.value_mem_region D p) ?_).symm
  exact groupingEquiv_rootValue D p

end
end JoshiTeich.Act1Scene1.DegreeBlockRegionGrouping
