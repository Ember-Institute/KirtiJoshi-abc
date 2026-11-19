import Solutions.Source_ReferenceIutConcreteLocalFiniteIndeterminacy
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionAlgebraNormGeneral
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorEqualNormHull
import Mathlib.RingTheory.Norm.Basic

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalConstruct

open NumberField
open JoshiTeich.Act1Scene1.LocalCompletion (padicAlgebra norm_algebraNorm_eq_completionNorm)
open scoped Pointwise TensorProduct

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]
variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)
variable (hc : ∀ i, IsOver K p (c i))

local instance factorAlgebra (i : ι) :
    Algebra ℚ_[p] ((genuinePacket p c hc).Factor i) :=
  padicAlgebra ((genuinePacket p c hc).residueChar_eq i)

/-- The inclusion of a completion into the uniform packet comes from a pure tensor
with one factor carrying the scalar. -/
theorem genuineTensorEquiv_pure_mulSingle (j : ι) (w : FinitePlace K)
    (h : c j = Place.finite w) (x : completionAt K w) :
    letI := Classical.decEq ι
    genuineTensorEquiv p c hc ((genuinePacket p c hc).pure
      (Pi.mulSingle j (completionCongr (eq_finPart h) x))) = incl p c j w h x := by
  classical
  rw [genuineTensorEquiv_pure, incl_apply, inclFactor, PiTensorProduct.singleAlgHom_apply]
  apply congrArg (PiTensorProduct.tprod ℚ_[p])
  funext i
  by_cases hi : i = j
  · subst i
    calc
      _ = factorMk p (c j) (completionCongr (eq_finPart h) x) :=
        congrArg (factorMk p (c j))
          (Pi.mulSingle_eq_same (M := fun k => completionAt K (finPart K (c k))) j
            (completionCongr (eq_finPart h) x))
      _ = _ := by simp [MonoidHom.mulSingle_apply]
  · calc
      _ = factorMk p (c i) (1 : completionAt K (finPart K (c i))) :=
        congrArg (factorMk p (c i))
          (Pi.mulSingle_eq_of_ne (M := fun k => completionAt K (finPart K (c k))) hi
            (completionCongr (eq_finPart h) x))
      _ = _ := by simp [MonoidHom.mulSingle_apply, hi]

/-- The transport of a principal region preserves its scaling element. -/
theorem genuineTensorEquiv_image_principalRegion (a : (genuinePacket p c hc).Tensor) :
    genuineTensorEquiv p c hc '' (genuinePacket p c hc).principalRegion a =
      genuineTensorEquiv p c hc a • integral p c := by
  rw [← genuineTensorEquiv_image_normalization p c hc]
  simp only [JoshiTeich.Act1Scene1.LocalCompletion.Packet.principalRegion, ← Set.image_smul,
    Set.image_image, smul_eq_mul, map_mul]

private theorem factorTensorAut_image_pure_principalRegion
    (σ : ∀ i, (genuinePacket p c hc).Factor i ≃ₐ[ℚ_[p]] (genuinePacket p c hc).Factor i)
    (z : ∀ i, (genuinePacket p c hc).Factor i) (hz : ∀ i, z i ≠ 0) :
    (genuinePacket p c hc).factorTensorAut σ ''
        (genuinePacket p c hc).principalRegion ((genuinePacket p c hc).pure z) =
      (genuinePacket p c hc).principalRegion ((genuinePacket p c hc).pure z) := by
  let P := genuinePacket p c hc
  let e := P.factorTensorAut σ
  let z' : ∀ i, P.Factor i := fun i => σ i (z i)
  have hz' (i : ι) : z' i ≠ 0 := (map_ne_zero_iff (σ i) (σ i).injective).mpr (hz i)
  have hn (i : ι) : ‖z' i‖ = ‖z i‖ := by
    letI := padicAlgebra (P.residueChar_eq i)
    calc
      ‖z' i‖ = ‖Algebra.norm ℚ_[p] (z' i)‖ :=
        (norm_algebraNorm_eq_completionNorm (P.place i) (P.residueChar_eq i) _ (hz' i)).symm
      _ = ‖Algebra.norm ℚ_[p] (z i)‖ := congrArg norm (Algebra.norm_eq_of_algEquiv (σ i) (z i))
      _ = _ := norm_algebraNorm_eq_completionNorm (P.place i) (P.residueChar_eq i) _ (hz i)
  have he : e (P.pure z) = P.pure z' := P.factorTensorMap_tprod σ z
  change e '' P.principalRegion (P.pure z) = P.principalRegion (P.pure z)
  calc
    e '' P.principalRegion (P.pure z) = P.principalRegion (P.pure z') := by
      have hinter : e '' (P.normalization : Set P.Tensor) = P.normalization :=
        P.factorTensorAut_image_normalization σ
      unfold JoshiTeich.Act1Scene1.LocalCompletion.Packet.principalRegion
      ext y
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        have hx' : e x ∈ (P.normalization : Set P.Tensor) := by
          rw [← hinter]
          exact ⟨x, hx, rfl⟩
        refine ⟨e x, hx', ?_⟩
        change P.pure z' * e x = e (P.pure z * x)
        rw [map_mul, he]
      · rintro ⟨x, hx, rfl⟩
        rw [← hinter] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        refine ⟨P.pure z * y, ⟨y, hy, rfl⟩, ?_⟩
        change e (P.pure z * y) = P.pure z' * e y
        rw [map_mul, he]
    _ = _ := by
      rw [← P.scalarNormalization_eq_principalRegion z' hz',
        ← P.scalarNormalization_eq_principalRegion z hz]
      exact P.scalarNormalization_eq_of_norm_eq z' z hz' hz hn

include hc in
/-- The finite indeterminacy orbit of a principal region scaled in one factor
equals that principal region. -/
theorem finiteIndAut_iUnion_incl_smul_integral (j : ι) (w : FinitePlace K)
    (h : c j = Place.finite w) (x : completionAt K w) (hx : x ≠ 0) :
    (⋃ φ ∈ finiteIndAut p c, φ '' (incl p c j w h x • integral p c)) =
      incl p c j w h x • integral p c := by
  classical
  let P := genuinePacket p c hc
  let z : ∀ i, P.Factor i := Pi.mulSingle j (completionCongr (eq_finPart h) x)
  have hz (i : ι) : z i ≠ 0 := by
    by_cases hi : i = j
    · subst i
      have hj : z j = completionCongr (eq_finPart h) x :=
        Pi.mulSingle_eq_same (M := fun k => P.Factor k) j _
      rw [hj]
      exact (map_ne_zero_iff (completionCongr (eq_finPart h))
        (completionCongr (eq_finPart h)).injective).mpr hx
    · have hj : z i = 1 := Pi.mulSingle_eq_of_ne (M := fun k => P.Factor k) hi _
      rw [hj]
      exact one_ne_zero
  have hregion :
      genuineTensorEquiv p c hc '' P.principalRegion (P.pure z) =
        incl p c j w h x • integral p c := by
    calc
      _ = genuineTensorEquiv p c hc (P.pure z) • integral p c :=
        genuineTensorEquiv_image_principalRegion p c hc (P.pure z)
      _ = _ := congrArg (· • integral p c) (genuineTensorEquiv_pure_mulSingle p c hc j w h x)
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨φ, hφ, hy⟩ := Set.mem_iUnion₂.mp hy
    rw [finiteIndAut_eq_image_of_isOver p c hc] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    obtain ⟨σ, rfl⟩ := hψ
    rw [← hregion, genuineTensorConjugate_image, factorTensorAut_image_pure_principalRegion p c hc
      σ z hz, hregion] at hy
    exact hy
  · intro y hy
    exact Set.mem_iUnion₂.mpr ⟨id, id_mem_finiteIndAut p c, ⟨y, hy, rfl⟩⟩

end

end AbcAdaptation.Reference.Iut.LocalConstruct
