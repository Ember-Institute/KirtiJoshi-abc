import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionPadicAlgebra
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLogBall
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.Algebra.Module.RingHom

/-!
source-id: JT-SCENE1-LOCAL-COMPLETION-TENSOR-LATTICE
source: Joshi III `ss:weighted-vol`, `le:volume-lemma2` and
`le:volume-lemma3`; the integral-generator construction of the reference
LocalConstruct Integral/LogShell API is used as an API guide.
fidelity: constructs the actual tensor of completions over one residue
prime and the integral spans of pure tensors. No tensor measure, maximal
order, hull or different-untilt identification is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion

open NumberField
open scoped TensorProduct BigOperators

universe u

/-- A finite tuple of actual completions over one rational prime. -/
structure Packet (K : Type u) [Field K] [NumberField K] (p : ℕ) (ι : Type) where
  place : ι → FinitePlace K
  residueChar_eq : ∀ i, JoshiTeich.Prologue.Arithmetic.residueChar (place i) = p

namespace Packet

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

abbrev Factor (i : ι) := completionAt K (P.place i)

noncomputable local instance factorAlgebra (i : ι) : Algebra ℚ_[p] (P.Factor i) :=
  padicAlgebra (P.residueChar_eq i)

local instance factorFinite (i : ι) : Module.Finite ℚ_[p] (P.Factor i) :=
  finite_padicAlgebra (P.residueChar_eq i)

local instance factorCharZero (i : ι) : CharZero (P.Factor i) :=
  charZero_of_injective_ringHom (FinitePlace.embedding (P.place i).maximalIdeal).injective

abbrev Tensor := ⨂[ℚ_[p]] i, P.Factor i

noncomputable local instance tensorIntegralModule : Module ℤ_[p] P.Tensor :=
  Module.compHom P.Tensor (algebraMap ℤ_[p] ℚ_[p])

/-- The tensor of a tuple, formed in the actual completion modules. -/
noncomputable def pure (a : ∀ i, P.Factor i) : P.Tensor := PiTensorProduct.tprod ℚ_[p] a

theorem pure_ne_zero (a : ∀ i, P.Factor i) (ha : ∀ i, a i ≠ 0) : P.pure a ≠ 0 := by
  classical
  let b := fun i => Module.finBasis ℚ_[p] (P.Factor i)
  have hEach (i : ι) : ∃ k, (b i).repr (a i) k ≠ 0 := by
    by_contra! h
    apply ha i
    apply (b i).repr.injective
    ext k
    simpa only [map_zero, Finsupp.zero_apply] using h k
  choose k hk using hEach
  intro hzero
  have h := congrArg (fun t : P.Tensor => (Basis.piTensorProduct b).repr t k) hzero
  rw [pure, Basis.piTensorProduct_repr_tprod_apply, map_zero, Finsupp.zero_apply] at h
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hk i)) h

/-- Integral linear combinations of pure tensors from the prescribed factor sets. -/
noncomputable def lattice (S : ∀ i, Set (P.Factor i)) : Submodule ℤ_[p] P.Tensor :=
  Submodule.span ℤ_[p] {t | ∃ a : ∀ i, P.Factor i, (∀ i, a i ∈ S i) ∧ P.pure a = t}

theorem pure_mem_lattice (S : ∀ i, Set (P.Factor i)) (a : ∀ i, P.Factor i)
    (ha : ∀ i, a i ∈ S i) : P.pure a ∈ P.lattice S :=
  Submodule.subset_span ⟨a, ha, rfl⟩

theorem lattice_mono {S T : ∀ i, Set (P.Factor i)} (h : ∀ i, S i ⊆ T i) :
    P.lattice S ≤ P.lattice T := by
  apply Submodule.span_mono
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a, fun i => h i (ha i), rfl⟩

/-- The tensor integral order before maximal-order normalization. -/
noncomputable def unitLattice : Submodule ℤ_[p] P.Tensor :=
  P.lattice (fun _ => Metric.closedBall 0 1)

/-- The integral span of pure tensors of ordinary local logarithm values. -/
noncomputable def tensorLogShell : Submodule ℤ_[p] P.Tensor :=
  P.lattice (fun i => LocalPadicLog.logShell (k := P.Factor i) p)

theorem unitLattice_le_tensorLogShell : P.unitLattice ≤ P.tensorLogShell := by
  apply P.lattice_mono
  intro i
  apply LocalPadicLog.closedBall_subset_logShell (Fact.out : p.Prime)
  have h := norm_natCast_prime_lt_one (P.residueChar_eq i)
  rwa [← FinitePlace.embedding_apply, map_natCast] at h

end Packet
end JoshiTeich.Act1Scene1.LocalCompletion
