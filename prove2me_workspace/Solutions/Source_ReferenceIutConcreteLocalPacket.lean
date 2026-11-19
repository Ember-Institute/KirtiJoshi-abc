/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/LocalConstruct/Packet.lean
-/

import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionPadicAlgebra
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalArchimedeanTensor
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Topology.MetricSpace.Ultra.Pi

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalConstruct

open NumberField IsDedekindDomain
open scoped TensorProduct

universe u

/-- Every rational prime, as an element of `Nat.Primes`, is a prime (as an instance). -/
instance instFactPrime (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

variable (K : Type u) [Field K] [NumberField K]

/-! ### Places over a prime -/

/-- A place is *over the prime `p`* if it is a finite place of residue characteristic `p`. -/
def IsOver (p : Nat.Primes) (v : Place K) : Prop :=
  ∃ w : FinitePlace K, v = Place.finite w ∧ residueChar w = p

variable {K}

lemma isOver_finite_iff (p : Nat.Primes) (w : FinitePlace K) :
    IsOver K p (Place.finite w) ↔ residueChar w = p := by
  refine ⟨fun ⟨w', hw', h⟩ => ?_, fun h => ⟨w, rfl, h⟩⟩
  cases Sum.inl.inj hw'
  exact h

lemma not_isOver_infinite (p : Nat.Primes) (w : InfinitePlace K) :
    ¬ IsOver K p (Place.infinite w) := by
  rintro ⟨w', hw', -⟩
  simp [Place.infinite, Place.finite] at hw'

/-- The number field `K` has a finite place. -/
instance : Nonempty (FinitePlace K) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨FinitePlace.mk ⟨M, hM.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩⟩

variable (K) in
/-- The finite place underlying a place (an arbitrary finite place at infinite places;
junk, never used in a meaningful way). -/
noncomputable def finPart : Place K → FinitePlace K :=
  Sum.elim id fun _ => Classical.arbitrary _

@[simp] lemma finPart_finite (w : FinitePlace K) : finPart K (Place.finite w) = w := rfl

lemma eq_finPart {v : Place K} {w : FinitePlace K} (h : v = Place.finite w) :
    w = finPart K v := by subst h; rfl

lemma IsOver.residueChar_finPart {p : Nat.Primes} {v : Place K} (h : IsOver K p v) :
    residueChar (finPart K v) = p := by
  obtain ⟨w, rfl, hw⟩ := h
  exact hw

/-- Transport of completions along an equality of finite places. -/
noncomputable def completionCongr {w w' : FinitePlace K} (h : w = w') :
    completionAt K w ≃+* completionAt K w' :=
  h ▸ RingEquiv.refl _

@[simp] lemma completionCongr_rfl (w : FinitePlace K) :
    completionCongr (rfl : w = w) = RingEquiv.refl _ := rfl

@[simp] lemma norm_completionCongr {w w' : FinitePlace K} (h : w = w') (x : completionAt K w) :
    ‖completionCongr h x‖ = ‖x‖ := by subst h; rfl

/-! ### The nonarchimedean factors -/

section Factor

variable (K)

open Classical in
/-- The junk ideal: `⊥` when `v` lies over `p` (so that the factor is the completion),
`⊤` otherwise (so that the factor is the zero ring). -/
noncomputable def junkIdeal (p : Nat.Primes) (v : Place K) : Ideal (completionAt K (finPart K v)) :=
  if IsOver K p v then ⊥ else ⊤

/-- **The nonarchimedean factor** attached to the prime `p` and the place `v`: the completion
`K_v` when `v` is a finite place of residue characteristic `p`, the zero ring otherwise. -/
def Factor (p : Nat.Primes) (v : Place K) : Type u :=
  completionAt K (finPart K v) ⧸ junkIdeal K p v

variable {K}

lemma junkIdeal_eq_bot {p : Nat.Primes} {v : Place K} (h : IsOver K p v) :
    junkIdeal K p v = ⊥ := by
  unfold junkIdeal
  rw [if_pos h]

lemma junkIdeal_eq_top {p : Nat.Primes} {v : Place K} (h : ¬ IsOver K p v) :
    junkIdeal K p v = ⊤ := by
  unfold junkIdeal
  rw [if_neg h]

variable (p : Nat.Primes) (v : Place K)

noncomputable instance : CommRing (Factor K p v) :=
  inferInstanceAs (CommRing (completionAt K (finPart K v) ⧸ junkIdeal K p v))

/-- The quotient map from the completion to the factor. -/
noncomputable def factorMk : completionAt K (finPart K v) →+* Factor K p v :=
  Ideal.Quotient.mk (junkIdeal K p v)

lemma factorMk_surjective : Function.Surjective (factorMk p v) :=
  Ideal.Quotient.mk_surjective

lemma factorMk_eq_zero_iff {x : completionAt K (finPart K v)} :
    factorMk p v x = 0 ↔ x ∈ junkIdeal K p v :=
  Ideal.Quotient.eq_zero_iff_mem

lemma factorMk_injective (h : IsOver K p v) : Function.Injective (factorMk p v) := by
  intro x y hxy
  rw [← sub_eq_zero, ← map_sub, factorMk_eq_zero_iff, junkIdeal_eq_bot h, Ideal.mem_bot,
    sub_eq_zero] at hxy
  exact hxy

lemma subsingleton_factor (h : ¬ IsOver K p v) : Subsingleton (Factor K p v) :=
  (Ideal.Quotient.subsingleton_iff (I := junkIdeal K p v)).mpr (junkIdeal_eq_top h)

/-- Nonzero elements of the completion are units in the factor (trivially so in the zero
ring). -/
lemma isUnit_factorMk {x : completionAt K (finPart K v)} (hx : x ≠ 0) :
    IsUnit (factorMk p v x) :=
  ⟨⟨factorMk p v x, factorMk p v x⁻¹, by rw [← map_mul, mul_inv_cancel₀ hx, map_one],
    by rw [← map_mul, inv_mul_cancel₀ hx, map_one]⟩, rfl⟩

/-- The trivial ring homomorphism into a subsingleton ring. -/
private def ringHomToSubsingleton (R S : Type*) [Semiring R] [Semiring S] [Subsingleton S] :
    R →+* S where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := rfl
  map_add' _ _ := Subsingleton.elim _ _

open Classical in
/-- The structure map `ℚ_p → Factor K p v`: the embedding `ℚ_p → K_v` followed by the quotient
map when `v ∣ p`, the trivial map to the zero ring otherwise. -/
noncomputable def factorAlgebraMap : ℚ_[p] →+* Factor K p v :=
  if h : IsOver K p v then (factorMk p v).comp
      (JoshiTeich.Act1Scene1.LocalCompletion.padicEmb h.residueChar_finPart)
  else
    haveI := subsingleton_factor p v h
    ringHomToSubsingleton _ _

lemma factorAlgebraMap_of_isOver (h : IsOver K p v) :
    factorAlgebraMap p v = (factorMk p v).comp
      (JoshiTeich.Act1Scene1.LocalCompletion.padicEmb h.residueChar_finPart) := by
  unfold factorAlgebraMap
  rw [dif_pos h]

noncomputable instance : Algebra ℚ_[p] (Factor K p v) := (factorAlgebraMap p v).toAlgebra

lemma algebraMap_factor : algebraMap ℚ_[p] (Factor K p v) = factorAlgebraMap p v := rfl

lemma algebraMap_factor_apply_of_isOver (h : IsOver K p v) (c : ℚ_[p]) :
    algebraMap ℚ_[p] (Factor K p v) c =
      factorMk p v (JoshiTeich.Act1Scene1.LocalCompletion.padicEmb h.residueChar_finPart c) := by
  rw [algebraMap_factor, factorAlgebraMap_of_isOver p v h]
  rfl

/-- The factors are finite-dimensional over `ℚ_p`. -/
instance : Module.Finite ℚ_[p] (Factor K p v) := by
  by_cases h : IsOver K p v
  · letI := JoshiTeich.Act1Scene1.LocalCompletion.padicAlgebra h.residueChar_finPart
    haveI := JoshiTeich.Act1Scene1.LocalCompletion.finite_padicAlgebra h.residueChar_finPart
    let f : completionAt K (finPart K v) →ₗ[ℚ_[p]] Factor K p v :=
      { toFun := factorMk p v
        map_add' := map_add _
        map_smul' := fun c x => by
          simp only [RingHom.id_apply]
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, algebraMap_factor_apply_of_isOver p v h]
          rfl }
    exact Module.Finite.of_surjective f (factorMk_surjective p v)
  · haveI := subsingleton_factor p v h
    exact Module.Finite.of_finite

lemma nontrivial_factor (h : IsOver K p v) : Nontrivial (Factor K p v) :=
  (factorMk_injective p v h).nontrivial

end Factor

/-! ### The archimedean factors -/

section ArchFactor

variable (K)

/-- The infinite place underlying a place (an arbitrary infinite place at finite places;
junk). -/
noncomputable def archPlace : Place K → InfinitePlace K :=
  Sum.elim (fun _ => Classical.arbitrary _) id

@[simp] lemma archPlace_infinite (w : InfinitePlace K) : archPlace K (Place.infinite w) = w := rfl

/-- The real or complex subalgebra of the completion at an infinite place. -/
noncomputable abbrev archField (w : InfinitePlace K) : Subalgebra ℝ ℂ :=
  JoshiTeich.Act1Scene1.LocalArchimedean.archField w

omit [NumberField K] in
lemma archField_of_isReal {w : InfinitePlace K} (h : w.IsReal) : archField K w = ⊥ :=
  JoshiTeich.Act1Scene1.LocalArchimedean.archField_of_isReal h

omit [NumberField K] in
lemma archField_of_isComplex {w : InfinitePlace K} (h : w.IsComplex) : archField K w = ⊤ :=
  JoshiTeich.Act1Scene1.LocalArchimedean.archField_of_isComplex h

/-- The archimedean factor selected by the infinite place associated to v. -/
abbrev ArchFactor (v : Place K) : Type u :=
  JoshiTeich.Act1Scene1.LocalArchimedean.Factor (archPlace K v)

end ArchFactor

/-! ### The base fields and the factors, uniformly in the rational place -/

/-- The base field of the packets at a rational place: `ℚ_p` at `p`, `ℝ` at `∞`. -/
abbrev baseField : RationalPlace → Type
  | .finite p => ℚ_[p]
  | .infinite => ℝ

noncomputable instance instNontriviallyNormedFieldBaseField (vQ : RationalPlace) :
    NontriviallyNormedField (baseField vQ) :=
  match vQ with
  | .finite p => inferInstanceAs (NontriviallyNormedField ℚ_[p])
  | .infinite => inferInstanceAs (NontriviallyNormedField ℝ)

instance instCompleteSpaceBaseField (vQ : RationalPlace) : CompleteSpace (baseField vQ) :=
  match vQ with
  | .finite p => inferInstanceAs (CompleteSpace ℚ_[p])
  | .infinite => inferInstanceAs (CompleteSpace ℝ)

instance instProperSpaceBaseField (vQ : RationalPlace) : ProperSpace (baseField vQ) :=
  match vQ with
  | .finite p => inferInstanceAs (ProperSpace ℚ_[p])
  | .infinite => inferInstanceAs (ProperSpace ℝ)

variable (K) in
/-- The factor attached to a rational place and a place of `K`. -/
abbrev Factor' : RationalPlace → Place K → Type u
  | .finite p => Factor K p
  | .infinite => ArchFactor K

noncomputable instance instCommRingFactor' (vQ : RationalPlace) (v : Place K) :
    CommRing (Factor' K vQ v) :=
  match vQ with
  | .finite p => inferInstanceAs (CommRing (Factor K p v))
  | .infinite => inferInstanceAs (CommRing (ArchFactor K v))

noncomputable instance instAlgebraFactor' (vQ : RationalPlace) (v : Place K) :
    Algebra (baseField vQ) (Factor' K vQ v) :=
  match vQ with
  | .finite p => inferInstanceAs (Algebra ℚ_[p] (Factor K p v))
  | .infinite => inferInstanceAs (Algebra ℝ (ArchFactor K v))

instance instFiniteFactor' (vQ : RationalPlace) (v : Place K) :
    Module.Finite (baseField vQ) (Factor' K vQ v) :=
  match vQ with
  | .finite p => inferInstanceAs (Module.Finite ℚ_[p] (Factor K p v))
  | .infinite => inferInstanceAs (Module.Finite ℝ (ArchFactor K v))

/-! ### The tensor packets -/

variable (K) in
/-- **The tensor packet** `⊗_j K_{c j}` over `ℚ_p` (at `v_ℚ = p`) or `ℝ` (at `v_ℚ = ∞`). -/
abbrev Tensor {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K) : Type u :=
  ⨂[baseField vQ] j, Factor' K vQ (c j)

section Tensor

variable {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → Place K)

/-- The index type of the basis of elementary tensors of the packet. -/
abbrev PacketIndex : Type := ∀ j, Fin (Module.finrank (baseField vQ) (Factor' K vQ (c j)))

noncomputable instance : Fintype (PacketIndex vQ c) :=
  match vQ with
  | .finite _ => by classical infer_instance
  | .infinite => JoshiTeich.Act1Scene1.LocalArchimedean.basisIndexFintype (fun j => archPlace K (c j))

/-- **The basis of elementary tensors** `⊗_j b_j(k_j)` of the packet, from chosen bases
`b_j` of the factors. -/
noncomputable def packetBasis :
    Module.Basis (PacketIndex vQ c) (baseField vQ) (Tensor K vQ c) :=
  match vQ with
  | .finite p => Basis.piTensorProduct fun j => Module.finBasis ℚ_[p] (Factor K p (c j))
  | .infinite => JoshiTeich.Act1Scene1.LocalArchimedean.tensorBasis (fun j => archPlace K (c j))

/-- **The norm of the packet**: the sup norm of the coordinates in the basis of elementary
tensors. Its topology is the unique Hausdorff vector space topology of the packet. -/
noncomputable instance instNormedAddCommGroupTensor : NormedAddCommGroup (Tensor K vQ c) :=
  NormedAddCommGroup.induced (Tensor K vQ c) (PacketIndex vQ c → baseField vQ)
    (packetBasis vQ c).equivFun (packetBasis vQ c).equivFun.injective

noncomputable instance instNormedSpaceTensor : NormedSpace (baseField vQ) (Tensor K vQ c) :=
  NormedSpace.induced (baseField vQ) (Tensor K vQ c) (PacketIndex vQ c → baseField vQ)
    (packetBasis vQ c).equivFun

lemma norm_def (x : Tensor K vQ c) : ‖x‖ = ‖(packetBasis vQ c).equivFun x‖ := rfl

lemma dist_def (x y : Tensor K vQ c) :
    dist x y = dist ((packetBasis vQ c).equivFun x) ((packetBasis vQ c).equivFun y) := rfl

/-- The packet carries the module topology. -/
instance instIsModuleTopologyTensor : IsModuleTopology (baseField vQ) (Tensor K vQ c) :=
  isModuleTopologyOfFiniteDimensional

/-- **The packet is a topological ring.** -/
instance instIsTopologicalRingTensor : IsTopologicalRing (Tensor K vQ c) :=
  IsModuleTopology.isTopologicalRing (baseField vQ) _

/-- **The packet is a proper (locally compact) space.** -/
instance instProperSpaceTensor : ProperSpace (Tensor K vQ c) :=
  FiniteDimensional.proper (baseField vQ) _

instance instSecondCountableTopologyTensor : SecondCountableTopology (Tensor K vQ c) := by
  haveI : SecondCountableTopology (PacketIndex vQ c → baseField vQ) := by
    haveI : ∀ vQ : RationalPlace, SecondCountableTopology (baseField vQ) := fun vQ =>
      match vQ with
      | .finite p =>
        haveI : TopologicalSpace.SeparableSpace ℚ_[p] :=
          ⟨⟨Set.range ((↑) : ℚ → ℚ_[p]), Set.countable_range _, Padic.denseRange_ratCast p⟩⟩
        inferInstanceAs (SecondCountableTopology ℚ_[p])
      | .infinite => inferInstanceAs (SecondCountableTopology ℝ)
    infer_instance
  exact (packetBasis vQ c).equivFunL.toHomeomorph.isInducing.secondCountableTopology

/-! The instances above are keyed on a variable rational place; instance search does not
find them at the constructors `.finite p` and `.infinite` (the base field reduces there),
so we restate them. -/

noncomputable instance (p : Nat.Primes) : NormedAddCommGroup (Tensor K (.finite p) c) :=
  instNormedAddCommGroupTensor (.finite p) c

noncomputable instance : NormedAddCommGroup (Tensor K .infinite c) :=
  instNormedAddCommGroupTensor .infinite c

instance (p : Nat.Primes) : IsTopologicalRing (Tensor K (.finite p) c) :=
  instIsTopologicalRingTensor (.finite p) c

instance : IsTopologicalRing (Tensor K .infinite c) := instIsTopologicalRingTensor .infinite c

instance (p : Nat.Primes) : ProperSpace (Tensor K (.finite p) c) :=
  instProperSpaceTensor (.finite p) c

instance : ProperSpace (Tensor K .infinite c) := instProperSpaceTensor .infinite c

instance (p : Nat.Primes) : SecondCountableTopology (Tensor K (.finite p) c) :=
  instSecondCountableTopologyTensor (.finite p) c

instance : SecondCountableTopology (Tensor K .infinite c) :=
  instSecondCountableTopologyTensor .infinite c

/-- The nonarchimedean packets are ultrametric. -/
instance (p : Nat.Primes) : IsUltrametricDist (Tensor K (.finite p) c) :=
  ⟨fun x y z => IsUltrametricDist.dist_triangle_max ((packetBasis (.finite p) c).equivFun x)
    ((packetBasis (.finite p) c).equivFun y) ((packetBasis (.finite p) c).equivFun z)⟩

/-- Specialization of the normed-space instance at a prime. -/
noncomputable instance (p : Nat.Primes) : NormedSpace ℚ_[p] (Tensor K (.finite p) c) :=
  instNormedSpaceTensor (.finite p) c

/-- Specialization of the normed-space instance at the archimedean place. -/
noncomputable instance : NormedSpace ℝ (Tensor K .infinite c) :=
  instNormedSpaceTensor .infinite c

end Tensor

/-! ### The inclusions of the factors -/

section Incl

variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K) (j : ι) (w : FinitePlace K)
  (h : c j = Place.finite w)

/-- The inclusion of the factor `Factor K p (c j)` into the packet, `a ↦ 1 ⊗ ⋯ ⊗ a ⊗ ⋯ ⊗ 1`. -/
noncomputable def inclFactor : Factor K p (c j) →ₐ[ℚ_[p]] Tensor K (.finite p) c :=
  haveI := Classical.decEq ι
  PiTensorProduct.singleAlgHom (R := ℚ_[p]) (A := fun j => Factor K p (c j)) j

/-- **The inclusion of the `j`-th tensor factor** `K_w → ⊗_i K_{c i}` at a nonarchimedean
place (`LocalTheory.incl`): `x ↦ 1 ⊗ ⋯ ⊗ x ⊗ ⋯ ⊗ 1`. -/
noncomputable def incl : completionAt K w →+* Tensor K (.finite p) c :=
  (inclFactor p c j).toRingHom.comp
    ((factorMk p (c j)).comp (completionCongr (eq_finPart h)).toRingHom)

lemma incl_apply (x : completionAt K w) :
    incl p c j w h x = inclFactor p c j (factorMk p (c j) (completionCongr (eq_finPart h) x)) :=
  rfl

/-- **Units of a factor are units of the packet** (`LocalTheory.isUnit_incl`). -/
lemma isUnit_incl (x : completionAt K w) (hx : x ≠ 0) : IsUnit (incl p c j w h x) := by
  rw [incl_apply]
  exact (isUnit_factorMk p (c j) ((map_ne_zero_iff _ (completionCongr _).injective).mpr hx)).map _

end Incl

/-- **The concrete tensor packets** as a `LocalTensor K`. -/
noncomputable def concreteLocalTensor : LocalTensor.{u, u} K where
  Tensor := Tensor K
  ring _ _ := inferInstance
  top _ _ := inferInstance
  algR _ := inferInstance

end AbcAdaptation.Reference.Iut.LocalConstruct
