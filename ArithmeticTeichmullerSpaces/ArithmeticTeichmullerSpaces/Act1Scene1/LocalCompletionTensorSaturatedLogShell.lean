import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionIntegralLogVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationLogVolume

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-SATURATED-LOG-SHELL
source: reference LocalConstruct/LogShell, tensorLogShell and logShell;
Joshi III tensor log-shells and principal hull (3568--3574).
fidelity: constructs the normalization-module span of the actual ordinary
completion tensor log-shell. Factor compactness gives bounded tensor span;
its positive Haar permits the proved normalization-hull/least-hull identity.
Derives compact openness, positive finite Haar, normalization containment,
and log-volume comparisons. No unramified identity, finite support, BK or
paper theta-locus identity is asserted. Original consumer proofs; no
reference source code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open JoshiTeich.Prologue NumberField MeasureTheory
open scoped BigOperators Classical

universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)
local instance shellFactorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)
local instance shellFactorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)
local instance shellFactorContinuousSMul (i : ι) : ContinuousSMul ℚ_[p] (P.Factor i) :=
  continuousSMul_of_algebraMap ℚ_[p] _ (continuous_padicEmb (P.residueChar_eq i))
local instance shellFactorModuleTopology (i : ι) : IsModuleTopology ℚ_[p] (P.Factor i) :=
  isModuleTopologyOfFiniteDimensional
local instance shellIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])
local instance shellBasisFintype : Fintype P.BasisIndex := by classical infer_instance

omit [Fact p.Prime] [Fintype ι] in
theorem factorLogShell_isCompact (i : ι) :
    IsCompact (LocalPadicLog.logShell (k := P.Factor i) p) := by
  simpa only [P.residueChar_eq i] using LocalCompletion.logShell_isCompact (P.place i)

omit [Fintype ι] in
theorem exists_factorLogShell_coordinate_bound (i : ι) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ a ∈ LocalPadicLog.logShell (k := P.Factor i) p, ∀ k,
      ‖(Module.finBasis ℚ_[p] (P.Factor i)).repr a k‖ ≤ C := by
  let b := Module.finBasis ℚ_[p] (P.Factor i)
  have hcont : Continuous b.equivFun :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    ((P.factorLogShell_isCompact i).image hcont).isBounded
  refine ⟨max C 0, le_max_right _ _, fun a ha k => ?_⟩
  exact (norm_le_pi_norm (b.equivFun a) k).trans
    ((hC (b.equivFun a) ⟨a, ha, rfl⟩).trans (le_max_left _ _))

theorem tensorLogShell_isBounded : Bornology.IsBounded (P.tensorLogShell : Set P.Tensor) := by
  choose C hC0 hC using P.exists_factorLogShell_coordinate_bound
  have hM : 0 ≤ ∏ i, C i := Finset.prod_nonneg fun i _ => hC0 i
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨∏ i, C i, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, ha, rfl⟩ := ht
    rw [tensor_norm_def, pi_norm_le_iff_of_nonneg hM]
    intro k
    rw [Module.Basis.equivFun_apply, tensorBasis, pure,
      Basis.piTensorProduct_repr_tprod_apply, norm_prod]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hC i (a i) (ha i) (k i)
  | zero => simpa only [norm_zero] using hM
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | smul r x _ hx =>
    change ‖(r : ℚ_[p]) • x‖ ≤ _
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one r)).trans hx

theorem tensorLogShell_isOpen : IsOpen (P.tensorLogShell : Set P.Tensor) := by
  apply AddSubgroup.isOpen_of_mem_nhds P.tensorLogShell.toAddSubgroup
  exact Filter.mem_of_superset
    ((P.lattice_balls_isOpen (fun _ => 1) (fun _ => zero_lt_one)).mem_nhds P.unitLattice.zero_mem)
    P.unitLattice_le_tensorLogShell

theorem tensorLogShell_isCompact : IsCompact (P.tensorLogShell : Set P.Tensor) :=
  (AddSubgroup.isClosed_of_isOpen P.tensorLogShell.toAddSubgroup P.tensorLogShell_isOpen).closure_eq ▸
    P.tensorLogShell_isBounded.isCompact_closure

theorem tensorLogShell_haar_pos : 0 < P.normalizationHaar P.tensorLogShell :=
  P.tensorLogShell_isOpen.measure_pos _ ⟨0, P.tensorLogShell.zero_mem⟩

def saturatedLogShell : Submodule P.normalization P.Tensor :=
  P.normalizationHull P.tensorLogShell

omit [Fintype ι] in
theorem tensorLogShell_subset_saturatedLogShell :
    (P.tensorLogShell : Set P.Tensor) ⊆ P.saturatedLogShell :=
  P.subset_normalizationHull _

theorem saturatedLogShell_eq_leastHull :
    (P.saturatedLogShell : Set P.Tensor) =
      P.leastHull P.tensorLogShell P.tensorLogShell_isBounded P.tensorLogShell_haar_pos :=
  P.normalizationHull_eq_leastHull _ _ _

theorem saturatedLogShell_isCompact : IsCompact (P.saturatedLogShell : Set P.Tensor) := by
  rw [P.saturatedLogShell_eq_leastHull]
  exact P.leastHull_isCompact _ _ _

theorem saturatedLogShell_isOpen : IsOpen (P.saturatedLogShell : Set P.Tensor) := by
  rw [P.saturatedLogShell_eq_leastHull]
  exact P.leastHull_isOpen _ _ _

theorem saturatedLogShell_haar_pos_lt_top :
    0 < P.normalizationHaar P.saturatedLogShell ∧ P.normalizationHaar P.saturatedLogShell < ⊤ := by
  rw [P.saturatedLogShell_eq_leastHull]
  exact P.leastHull_haar_pos_lt_top _ _ _

theorem normalization_subset_saturatedLogShell :
    (P.normalization : Set P.Tensor) ⊆ P.saturatedLogShell := by
  intro x hx
  have hone : (1 : P.Tensor) ∈ P.saturatedLogShell :=
    P.tensorLogShell_subset_saturatedLogShell (P.unitLattice_le_tensorLogShell P.one_mem_unitLattice)
  have h := P.saturatedLogShell.smul_mem (⟨x, hx⟩ : P.normalization) hone
  change x * 1 ∈ P.saturatedLogShell at h
  rwa [mul_one] at h

omit [Fintype ι] in
theorem saturatedLogShell_mul_mem {a x : P.Tensor} (ha : a ∈ P.normalization)
    (hx : x ∈ P.saturatedLogShell) : a * x ∈ P.saturatedLogShell :=
  P.saturatedLogShell.smul_mem (⟨a, ha⟩ : P.normalization) hx

omit [Fintype ι] in
theorem saturatedLogShell_le_iff (L : Submodule P.normalization P.Tensor) :
    P.saturatedLogShell ≤ L ↔ (P.tensorLogShell : Set P.Tensor) ⊆ L :=
  P.normalizationHull_le_iff _ _

theorem saturatedLogShell_normalizationLogVolume_nonneg :
    0 ≤ P.normalizationLogVolume P.saturatedLogShell := by
  have h := P.normalizationLogVolume_mono P.normalization_subset_saturatedLogShell
    (by rw [P.normalizationHaar_normalization]; exact zero_lt_one)
    P.saturatedLogShell_haar_pos_lt_top.2.ne
  simpa only [normalizationLogVolume, P.normalizationHaar_normalization,
    ENNReal.toReal_one, Real.log_one, zero_div] using h

theorem tensorLogShell_logVolume_le_saturatedLogShell :
    P.normalizationLogVolume P.tensorLogShell ≤ P.normalizationLogVolume P.saturatedLogShell :=
  P.normalizationLogVolume_mono P.tensorLogShell_subset_saturatedLogShell P.tensorLogShell_haar_pos
    P.saturatedLogShell_haar_pos_lt_top.2.ne

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
