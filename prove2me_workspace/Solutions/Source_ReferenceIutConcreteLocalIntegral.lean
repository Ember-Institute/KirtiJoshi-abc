/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/LocalConstruct/Integral.lean
  and Iut/Concrete/LocalConstruct/MaximalOrder.lean
-/
import Solutions.Source_ReferenceIutConcreteLocalPacketEquiv
import Solutions.Source_ReferenceIutConcreteLocalOrder
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationCompact

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalConstruct

open NumberField
open scoped TensorProduct Pointwise

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)

/-- The action of `ℤ_p` on the packet is the restriction of its `ℚ_p`-action. -/
instance instAlgebraPadicIntTensor : Algebra ℤ_[p] (Tensor K (.finite p) c) where
  smul r x := (r : ℚ_[p]) • x
  algebraMap := (algebraMap ℚ_[p] (Tensor K (.finite p) c)).comp (algebraMap ℤ_[p] ℚ_[p])
  commutes' r x := Algebra.commutes (r : ℚ_[p]) x
  smul_def' r x := Algebra.smul_def (r : ℚ_[p]) x

lemma algebraMap_padicInt_apply (r : ℤ_[p]) :
    algebraMap ℤ_[p] (Tensor K (.finite p) c) r = algebraMap ℚ_[p] _ (r : ℚ_[p]) := rfl

instance : IsScalarTower ℤ_[p] ℚ_[p] (Tensor K (.finite p) c) :=
  ⟨fun r s x => by
    change ((r : ℚ_[p]) * s) • x = (r : ℚ_[p]) • s • x
    exact mul_smul _ _ _⟩

/-- The tensor comparison also commutes with the integral scalars. -/
def genuineTensorIntegralEquiv (hc : ∀ j, IsOver K p (c j)) :
    (genuinePacket p c hc).Tensor ≃ₐ[ℤ_[p]] Tensor K (.finite p) c :=
  { (genuineTensorEquiv p c hc).toRingEquiv with
    commutes' := fun r => (genuineTensorEquiv p c hc).commutes (r : ℚ_[p]) }

/-- Families of elements in the completion unit balls. -/
abbrev IntegralTuple : Type u := ∀ j, {x : completionAt K (finPart K (c j)) // ‖x‖ ≤ 1}

/-- The pure tensor of an integral tuple, using the quotient maps on its factors. -/
def tprodIntegral (a : IntegralTuple c) : Tensor K (.finite p) c :=
  PiTensorProduct.tprod ℚ_[p] fun j => factorMk p (c j) (a j).1

def integralSet : Set (Tensor K (.finite p) c) := Set.range (tprodIntegral p c)

/-- The order `R_I` is the `ℤ_p`-span of the pure tensors of integral tuples. -/
def orderSubmodule : Submodule ℤ_[p] (Tensor K (.finite p) c) :=
  Submodule.span ℤ_[p] (integralSet p c)

def order : Set (Tensor K (.finite p) c) := orderSubmodule p c

lemma tprodIntegral_mem (a : IntegralTuple c) : tprodIntegral p c a ∈ order p c :=
  Submodule.subset_span ⟨a, rfl⟩

lemma one_mem_order : (1 : Tensor K (.finite p) c) ∈ order p c := by
  let a : IntegralTuple c := fun _ => ⟨1, by simp⟩
  have ha : tprodIntegral p c a = 1 := by
    rw [PiTensorProduct.one_def]
    exact congrArg (PiTensorProduct.tprod ℚ_[p]) (funext fun j => map_one (factorMk p (c j)))
  exact ha ▸ tprodIntegral_mem p c a

lemma genuineTensorEquiv_map_unitLattice (hc : ∀ j, IsOver K p (c j)) :
    (genuinePacket p c hc).unitLattice.map (genuineTensorIntegralEquiv p c hc).toLinearMap =
      orderSubmodule p c := by
  let S : Set (genuinePacket p c hc).Tensor :=
    {t | ∃ a : ∀ j, completionAt K (finPart K (c j)),
      (∀ j, a j ∈ Metric.closedBall 0 1) ∧ (genuinePacket p c hc).pure a = t}
  let e := (genuineTensorIntegralEquiv p c hc).toLinearMap
  change (Submodule.span ℤ_[p] S).map e = Submodule.span ℤ_[p] (integralSet p c)
  refine (Submodule.map_span e S).trans (congrArg (Submodule.span ℤ_[p]) ?_)
  refine Set.ext fun x => ?_
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    let b : IntegralTuple c := fun j =>
      ⟨a j, by
        have hj := ha j
        rw [Metric.mem_closedBall, dist_zero_right] at hj
        exact hj⟩
    exact ⟨b, (genuineTensorEquiv_pure p c hc a).symm⟩
  · rintro ⟨b, rfl⟩
    let a : ∀ j, completionAt K (finPart K (c j)) := fun j => (b j).1
    have ha (j : ι) : a j ∈ Metric.closedBall 0 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (b j).2
    exact ⟨(genuinePacket p c hc).pure a, ⟨a, ha, rfl⟩, genuineTensorEquiv_pure p c hc a⟩

theorem genuineTensorEquiv_image_unitLattice (hc : ∀ j, IsOver K p (c j)) :
    genuineTensorEquiv p c hc '' ↑((genuinePacket p c hc).unitLattice) = order p c := by
  exact congrArg (fun L : Submodule ℤ_[p] (Tensor K (.finite p) c) =>
    (L : Set (Tensor K (.finite p) c))) (genuineTensorEquiv_map_unitLattice p c hc)

/-- A zero factor makes the tensor a zero ring. -/
lemma subsingleton_tensor_of_not_isOver (j : ι) (hj : ¬ IsOver K p (c j)) :
    Subsingleton (Tensor K (.finite p) c) := by
  have := subsingleton_factor p (c j) hj
  have h : (0 : Factor K p (c j)) = 1 := Subsingleton.elim _ _
  have heq := congrArg (inclFactor p c j) h
  rw [map_zero, map_one] at heq
  exact subsingleton_of_zero_eq_one heq

private lemma order_eq_univ_of_subsingleton [Subsingleton (Tensor K (.finite p) c)] :
    order p c = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rw [Subsingleton.elim x 1]
  exact one_mem_order p c

theorem mul_mem_order {x y : Tensor K (.finite p) c} (hx : x ∈ order p c)
    (hy : y ∈ order p c) : x * y ∈ order p c := by
  classical
  by_cases hc : ∀ j, IsOver K p (c j)
  · rw [← genuineTensorEquiv_image_unitLattice p c hc] at hx hy ⊢
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨x' * y', (genuinePacket p c hc).mul_mem_unitLattice hx' hy', map_mul _ _ _⟩
  · obtain ⟨j, hj⟩ := not_forall.mp hc
    have := subsingleton_tensor_of_not_isOver p c j hj
    rw [order_eq_univ_of_subsingleton p c]
    exact Set.mem_univ _

/-- The pure tensor order as a `ℤ_p`-subalgebra. -/
def orderSubalgebra : Subalgebra ℤ_[p] (Tensor K (.finite p) c) where
  carrier := order p c
  mul_mem' := mul_mem_order p c
  one_mem' := one_mem_order p c
  add_mem' := (orderSubmodule p c).add_mem
  zero_mem' := (orderSubmodule p c).zero_mem
  algebraMap_mem' r := by
    change algebraMap ℤ_[p] (Tensor K (.finite p) c) r ∈ orderSubmodule p c
    rw [Algebra.algebraMap_eq_smul_one]
    exact (orderSubmodule p c).smul_mem r (one_mem_order p c)

/-- The finite integral structure is the integral closure of `ℤ_p` in the packet. -/
def integral : Set (Tensor K (.finite p) c) :=
  integralClosure ℤ_[p] (Tensor K (.finite p) c)

lemma mem_integral {x : Tensor K (.finite p) c} : x ∈ integral p c ↔ IsIntegral ℤ_[p] x := Iff.rfl

lemma one_mem_integral : (1 : Tensor K (.finite p) c) ∈ integral p c :=
  (integralClosure ℤ_[p] (Tensor K (.finite p) c)).one_mem

lemma integral_nonempty : (integral p c).Nonempty := ⟨1, one_mem_integral p c⟩

lemma mul_mem_integral {x y : Tensor K (.finite p) c} (hx : x ∈ integral p c)
    (hy : y ∈ integral p c) : x * y ∈ integral p c :=
  (integralClosure ℤ_[p] (Tensor K (.finite p) c)).mul_mem hx hy

lemma integral_eq_univ_of_subsingleton [Subsingleton (Tensor K (.finite p) c)] :
    integral p c = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rw [Subsingleton.elim x 1]
  exact one_mem_integral p c

theorem genuineTensorEquiv_image_normalization (hc : ∀ j, IsOver K p (c j)) :
    genuineTensorEquiv p c hc '' ↑((genuinePacket p c hc).normalization) = integral p c := by
  let e := genuineTensorIntegralEquiv p c hc
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change IsIntegral ℤ_[p] (e y)
    exact (isIntegral_algHom_iff e.toAlgHom e.injective).mpr hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change IsIntegral ℤ_[p] (e.symm x)
    exact (isIntegral_algHom_iff e.symm.toAlgHom e.symm.injective).mpr hx

theorem order_subset_integral : order p c ⊆ integral p c := by
  classical
  by_cases hc : ∀ j, IsOver K p (c j)
  · rw [← genuineTensorEquiv_image_unitLattice p c hc, ← genuineTensorEquiv_image_normalization p c hc]
    exact Set.image_mono (genuinePacket p c hc).unitLattice_le_normalization
  · obtain ⟨j, hj⟩ := not_forall.mp hc
    have := subsingleton_tensor_of_not_isOver p c j hj
    rw [integral_eq_univ_of_subsingleton p c]
    exact Set.subset_univ _

theorem order_isCompact_isOpen : IsCompact (order p c) ∧ IsOpen (order p c) := by
  classical
  by_cases hc : ∀ j, IsOver K p (c j)
  · rw [← genuineTensorEquiv_image_unitLattice p c hc]
    let e := (genuineTensorContinuousLinearEquiv p c hc).toHomeomorph
    exact ⟨((genuinePacket p c hc).lattice_balls_isCompact (fun _ => 1)
      (fun _ => zero_lt_one) (fun _ => le_rfl)).image e.continuous,
      e.isOpenMap _ ((genuinePacket p c hc).lattice_balls_isOpen (fun _ => 1) (fun _ => zero_lt_one))⟩
  · obtain ⟨j, hj⟩ := not_forall.mp hc
    have := subsingleton_tensor_of_not_isOver p c j hj
    rw [order_eq_univ_of_subsingleton p c]
    exact ⟨isCompact_univ, isOpen_univ⟩

private theorem integral_isCompact_isOpen : IsCompact (integral p c) ∧ IsOpen (integral p c) := by
  classical
  by_cases hc : ∀ j, IsOver K p (c j)
  · rw [← genuineTensorEquiv_image_normalization p c hc]
    let e := (genuineTensorContinuousLinearEquiv p c hc).toHomeomorph
    exact ⟨(genuinePacket p c hc).normalization_isCompact.image e.continuous,
      e.isOpenMap _ (genuinePacket p c hc).normalization_isOpen⟩
  · obtain ⟨j, hj⟩ := not_forall.mp hc
    have := subsingleton_tensor_of_not_isOver p c j hj
    rw [integral_eq_univ_of_subsingleton p c]
    exact ⟨isCompact_univ, isOpen_univ⟩

theorem isCompact_integral : IsCompact (integral p c) := (integral_isCompact_isOpen p c).1

theorem isOpen_integral : IsOpen (integral p c) := (integral_isCompact_isOpen p c).2

/-- The inclusion of a factor unit-ball element is a pure integral tensor. -/
lemma incl_mem_order (j : ι) (w : FinitePlace K) (h : c j = Place.finite w)
    (x : completionAt K w) (hx : ‖x‖ ≤ 1) : incl p c j w h x ∈ order p c := by
  classical
  let x' := completionCongr (eq_finPart h) x
  let a : IntegralTuple c := fun i =>
    ⟨Function.update (fun i => (1 : completionAt K (finPart K (c i)))) j x' i, by
      by_cases hi : i = j
      · subst i
        simpa only [Function.update_self, x', norm_completionCongr] using hx
      · simp [Function.update_of_ne hi]⟩
  have heq : incl p c j w h x = tprodIntegral p c a := by
    rw [incl_apply]
    unfold inclFactor tprodIntegral
    rw [PiTensorProduct.singleAlgHom_apply]
    apply congrArg (PiTensorProduct.tprod ℚ_[p])
    funext i
    by_cases hi : i = j
    · subst i
      simp [a, MonoidHom.mulSingle_apply, x']
    · simp [a, MonoidHom.mulSingle_apply, hi]
  rw [heq]
  exact tprodIntegral_mem p c a

lemma incl_mem_integral (j : ι) (w : FinitePlace K) (h : c j = Place.finite w)
    (x : completionAt K w) (hx : ‖x‖ ≤ 1) : incl p c j w h x ∈ integral p c :=
  order_subset_integral p c (incl_mem_order p c j w h x hx)

lemma smul_integral_subset (j : ι) (w : FinitePlace K) (h : c j = Place.finite w)
    (x : completionAt K w) (hx : ‖x‖ ≤ 1) :
    incl p c j w h x • integral p c ⊆ integral p c := by
  rintro _ ⟨y, hy, rfl⟩
  exact mul_mem_integral p c (incl_mem_integral p c j w h x hx) hy

lemma smul_integral_subset_of_ordp (j : ι) (w : FinitePlace K) (h : c j = Place.finite w)
    (x : completionAt K w) (_hx : x ≠ 0) (hord : 0 ≤ ordp K w x) :
    incl p c j w h x • integral p c ⊆ integral p c :=
  smul_integral_subset p c j w h x (norm_le_one_of_ordp_nonneg hord)

end

end AbcAdaptation.Reference.Iut.LocalConstruct
