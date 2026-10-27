import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedDegreeBlockVolume
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
source-id: JT-SCENE1-INITIAL-THETA-DEGREE-BLOCK-TENSOR-GROUPING
source: Joshi III `ss:weighted-vol` and `eq:weights`, the computed actual
moduli-degree partition, and Mathlib's multilinear composition and tensor bases.
fidelity: constructs the linear grouping map from the original completion
tensor to the tensor of its actual degree-block tensors. Its pure-tensor
law, coefficient identity, injectivity and dimension identity give an actual
linear equivalence. The existing log-root input consumes this equivalence.
boundary: Scene1/Derived; algebraic grouping only. No identification of
block-region volume with an ungraded region volume, paper carrier, global
holomorphoid or theta-volume is assumed. Original proofs; no reference code copied.
-/

namespace JoshiTeich.Act1Scene1.DegreeBlockTensorGrouping

open JoshiTeich.Prologue SelectedDegreeBlockVolume
open scoped BigOperators TensorProduct Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) [Fact p.Prime]

local instance factorAlgebra (i : Index D p) :
    Algebra ℚ_[p] ((SelectedThetaTensor.packet D p).Factor i) :=
  LocalCompletion.padicAlgebra ((SelectedThetaTensor.packet D p).residueChar_eq i)

local instance factorFinite (i : Index D p) :
    Module.Finite ℚ_[p] ((SelectedThetaTensor.packet D p).Factor i) :=
  LocalCompletion.finite_padicAlgebra ((SelectedThetaTensor.packet D p).residueChar_eq i)

local instance blockFactorAlgebra (d : DegreeSupport D p) (i : DegreeFiber D p d) :
    Algebra ℚ_[p] ((degreePacket D p d).Factor i) :=
  LocalCompletion.padicAlgebra ((degreePacket D p d).residueChar_eq i)

local instance blockFinite (d : DegreeSupport D p) :
    Module.Finite ℚ_[p] (degreePacket D p d).Tensor :=
  Module.Finite.of_basis (degreePacket D p d).tensorBasis

local instance originalFinite : Module.Finite ℚ_[p] (SelectedThetaTensor.packet D p).Tensor :=
  Module.Finite.of_basis (SelectedThetaTensor.packet D p).tensorBasis

def blockIndexEquiv : Index D p ≃ Σ d : DegreeSupport D p, DegreeFiber D p d where
  toFun := indexSigmaEquiv D p
  invFun s := s.2.1
  left_inv i := rfl
  right_inv s := by
    rcases s with ⟨⟨d, hd⟩, ⟨i, hi⟩⟩
    change Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p i) = d at hi
    subst d
    rfl

abbrev GroupedTensor := ⨂[ℚ_[p]] d : DegreeSupport D p, (degreePacket D p d).Tensor

def groupedMultilinear :
    MultilinearMap ℚ_[p] (fun s : Σ d : DegreeSupport D p, DegreeFiber D p d =>
      (degreePacket D p s.1).Factor s.2) (GroupedTensor D p) :=
  (PiTensorProduct.tprod ℚ_[p] : MultilinearMap ℚ_[p]
    (fun d : DegreeSupport D p => (degreePacket D p d).Tensor) (GroupedTensor D p)).compMultilinearMap
    (fun d => (PiTensorProduct.tprod ℚ_[p] : MultilinearMap ℚ_[p]
      (fun i : DegreeFiber D p d => (degreePacket D p d).Factor i) (degreePacket D p d).Tensor))

def groupingMultilinear :
    MultilinearMap ℚ_[p] (fun i => (SelectedThetaTensor.packet D p).Factor i)
      (GroupedTensor D p) :=
  (MultilinearMap.domDomCongrLinearEquiv' ℚ_[p] ℚ_[p]
    (fun s : Σ d : DegreeSupport D p, DegreeFiber D p d =>
      (degreePacket D p s.1).Factor s.2) (GroupedTensor D p) (blockIndexEquiv D p).symm)
    (groupedMultilinear D p)

def groupingLinear : (SelectedThetaTensor.packet D p).Tensor →ₗ[ℚ_[p]] GroupedTensor D p :=
  PiTensorProduct.lift (groupingMultilinear D p)

theorem groupingLinear_pure (z : ∀ i, (SelectedThetaTensor.packet D p).Factor i) :
    groupingLinear D p ((SelectedThetaTensor.packet D p).pure z) =
      PiTensorProduct.tprod ℚ_[p] (fun d => (degreePacket D p d).pure (fun i => z i.1)) := by
  rw [groupingLinear, LocalCompletion.Packet.pure, PiTensorProduct.lift.tprod]
  dsimp [groupingMultilinear, groupedMultilinear,
    MultilinearMap.domDomCongrLinearEquiv', MultilinearMap.compMultilinearMap]
  apply congrArg (PiTensorProduct.tprod ℚ_[p])
  funext d
  apply congrArg (PiTensorProduct.tprod ℚ_[p])
  funext i
  rcases d with ⟨d, hd⟩
  rcases i with ⟨i, hi⟩
  change Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p i) = d at hi
  subst d
  rfl

def blockBasis (d : DegreeSupport D p) :
    Module.Basis (degreePacket D p d).BasisIndex ℚ_[p] (degreePacket D p d).Tensor :=
  Basis.piTensorProduct (fun i : DegreeFiber D p d =>
    Module.finBasis ℚ_[p] ((SelectedThetaTensor.packet D p).Factor i.1))

def groupedBasis : Module.Basis (∀ d : DegreeSupport D p, (degreePacket D p d).BasisIndex)
    ℚ_[p] (GroupedTensor D p) :=
  Basis.piTensorProduct (blockBasis D p)

def blockBasisIndex (k : (SelectedThetaTensor.packet D p).BasisIndex)
    (d : DegreeSupport D p) : (degreePacket D p d).BasisIndex := fun i => k i.1

omit [Fact p.Prime] in
private theorem prod_blocks {M : Type*} [CommMonoid M] (f : Index D p → M) :
    (∏ d : DegreeSupport D p, ∏ i : DegreeFiber D p d, f i.1) = ∏ i, f i := by
  rw [← Fintype.prod_sigma' (fun (d : DegreeSupport D p) (i : DegreeFiber D p d) => f i.1)]
  exact Fintype.prod_equiv (blockIndexEquiv D p).symm _ _ (fun _ => rfl)

theorem blockBasis_repr_pure (d : DegreeSupport D p)
    (z : ∀ i, (SelectedThetaTensor.packet D p).Factor i)
    (k : (SelectedThetaTensor.packet D p).BasisIndex) :
    (blockBasis D p d).repr ((degreePacket D p d).pure (fun i => z i.1))
        (blockBasisIndex D p k d) =
      ∏ i : DegreeFiber D p d,
        (Module.finBasis ℚ_[p] ((SelectedThetaTensor.packet D p).Factor i.1)).repr
          (z i.1) (k i.1) := by
  exact Basis.piTensorProduct_repr_tprod_apply _ _ _

theorem groupedBasis_repr_pure (z : ∀ i, (SelectedThetaTensor.packet D p).Factor i)
    (k : (SelectedThetaTensor.packet D p).BasisIndex) :
    (groupedBasis D p).repr
        (PiTensorProduct.tprod ℚ_[p] (fun d => (degreePacket D p d).pure (fun i => z i.1)))
        (blockBasisIndex D p k) =
      (SelectedThetaTensor.packet D p).tensorBasis.repr
        ((SelectedThetaTensor.packet D p).pure z) k := by
  change (Basis.piTensorProduct (blockBasis D p)).repr _ _ = _
  rw [Basis.piTensorProduct_repr_tprod_apply]
  simp_rw [blockBasis_repr_pure D p]
  exact (prod_blocks D p (fun i =>
    (Module.finBasis ℚ_[p] ((SelectedThetaTensor.packet D p).Factor i)).repr (z i) (k i))).trans
      (Basis.piTensorProduct_repr_tprod_apply _ _ _).symm

def groupedCoordinate (k : (SelectedThetaTensor.packet D p).BasisIndex) :
    (SelectedThetaTensor.packet D p).Tensor →ₗ[ℚ_[p]] ℚ_[p] :=
  (Finsupp.lapply (blockBasisIndex D p k)).comp
    ((groupedBasis D p).repr.toLinearMap.comp (groupingLinear D p))

def originalCoordinate (k : (SelectedThetaTensor.packet D p).BasisIndex) :
    (SelectedThetaTensor.packet D p).Tensor →ₗ[ℚ_[p]] ℚ_[p] :=
  (Finsupp.lapply k).comp (SelectedThetaTensor.packet D p).tensorBasis.repr.toLinearMap

theorem groupedCoordinate_eq (k : (SelectedThetaTensor.packet D p).BasisIndex) :
    groupedCoordinate D p k = originalCoordinate D p k := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro z
  change (groupedBasis D p).repr
      (groupingLinear D p ((SelectedThetaTensor.packet D p).pure z))
        (blockBasisIndex D p k) = _
  rw [groupingLinear_pure]
  exact groupedBasis_repr_pure D p z k

theorem groupingLinear_repr (x : (SelectedThetaTensor.packet D p).Tensor)
    (k : (SelectedThetaTensor.packet D p).BasisIndex) :
    (groupedBasis D p).repr (groupingLinear D p x) (blockBasisIndex D p k) =
      (SelectedThetaTensor.packet D p).tensorBasis.repr x k :=
  LinearMap.congr_fun (groupedCoordinate_eq D p k) x

theorem groupingLinear_injective : Function.Injective (groupingLinear D p) := by
  intro x y h
  apply (SelectedThetaTensor.packet D p).tensorBasis.repr.injective
  ext k
  rw [← groupingLinear_repr D p x k, ← groupingLinear_repr D p y k, h]

theorem groupedTensor_finrank :
    Module.finrank ℚ_[p] (GroupedTensor D p) =
      Module.finrank ℚ_[p] (SelectedThetaTensor.packet D p).Tensor := by
  calc
    _ = ∏ d : DegreeSupport D p, Module.finrank ℚ_[p] (degreePacket D p d).Tensor := by
      rw [Module.finrank_eq_card_basis (groupedBasis D p), Fintype.card_pi]
      apply Finset.prod_congr rfl
      intro d _
      exact (Module.finrank_eq_card_basis (blockBasis D p d)).symm
    _ = ∏ d : DegreeSupport D p, ∏ i : DegreeFiber D p d,
        Arithmetic.localDeg ((SelectedThetaTensor.packet D p).place i.1) := by
      apply Finset.prod_congr rfl
      intro d _
      exact (degreePacket D p d).tensor_finrank_eq_localDeg_prod
    _ = _ := (prod_blocks D p (fun i =>
      Arithmetic.localDeg ((SelectedThetaTensor.packet D p).place i))).trans
        (SelectedThetaTensor.packet D p).tensor_finrank_eq_localDeg_prod.symm

def groupingEquiv : (SelectedThetaTensor.packet D p).Tensor ≃ₗ[ℚ_[p]] GroupedTensor D p :=
  LinearMap.linearEquivOfInjective (groupingLinear D p) (groupingLinear_injective D p)
    (groupedTensor_finrank D p).symm

theorem groupingEquiv_pure (z : ∀ i, (SelectedThetaTensor.packet D p).Factor i) :
    groupingEquiv D p ((SelectedThetaTensor.packet D p).pure z) =
      PiTensorProduct.tprod ℚ_[p] (fun d => (degreePacket D p d).pure (fun i => z i.1)) :=
  groupingLinear_pure D p z

def groupedRootValue : GroupedTensor D p :=
  PiTensorProduct.tprod ℚ_[p] (fun d => (degreePacket D p d).pure
    (fun i => iutInitialThetaFullQRootLogValue D (SelectedThetaTensor.sourceAt D p i.1)))

theorem groupingEquiv_rootValue :
    groupingEquiv D p (SelectedThetaTensor.value D p) = groupedRootValue D p :=
  groupingEquiv_pure D p _

theorem groupedRootValue_ne_zero : groupedRootValue D p ≠ 0 := by
  rw [← groupingEquiv_rootValue D p]
  intro hzero
  apply SelectedThetaTensor.value_ne_zero D p
  apply groupingLinear_injective D p
  change groupingLinear D p (SelectedThetaTensor.value D p) = groupingLinear D p 0
  rw [(groupingLinear D p).map_zero]
  exact hzero

end
end JoshiTeich.Act1Scene1.DegreeBlockTensorGrouping
