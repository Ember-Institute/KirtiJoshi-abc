import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorNormalizationCompact
import Mathlib.Algebra.Algebra.Pi

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-NORMALIZATION-DECOMPOSITION
source: actual reduced Artinian tensor decomposition, finite residue integral
closures and Mathlib integrality under injective algebra maps.
fidelity: proves integrality is equivalent to coordinate integrality and
constructs the Z_p-algebra decomposition of the actual normalization into
the product of residue-field integral closures. No residue norm or theta
locus is assumed. Original proofs; no reference code copied.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

theorem isIntegral_iff_residue_integral (x : P.Tensor) :
    IsIntegral ℤ_[p] x ↔ ∀ I : MaximalSpectrum P.Tensor,
      IsIntegral ℤ_[p] (Ideal.Quotient.mk I.asIdeal x) := by
  constructor
  · intro hx I
    exact IsIntegral.map_of_comp_eq (RingHom.id ℤ_[p]) (Ideal.Quotient.mk I.asIdeal)
      (RingHom.ext fun _ => rfl) hx
  · intro hx
    haveI := fun I => P.residueNormalization_module_finite I
    let A : MaximalSpectrum P.Tensor → Type u :=
      fun I => integralClosure ℤ_[p] (P.Tensor ⧸ I.asIdeal)
    let y : ∀ I, A I := fun I => ⟨Ideal.Quotient.mk I.asIdeal x, hx I⟩
    let f : (∀ I, A I) →ₐ[ℤ_[p]] (∀ I : MaximalSpectrum P.Tensor, P.Tensor ⧸ I.asIdeal) :=
      AlgHom.pi fun I => (integralClosure ℤ_[p] (P.Tensor ⧸ I.asIdeal)).val.comp
        (Pi.evalAlgHom ℤ_[p] A I)
    have hy : IsIntegral ℤ_[p] (f y) :=
      IsIntegral.map_of_comp_eq (RingHom.id ℤ_[p]) f.toRingHom
        (RingHom.ext fun r => (f.commutes r).symm) (IsIntegral.of_finite ℤ_[p] y)
    let e : P.Tensor →ₐ[ℤ_[p]] (∀ I : MaximalSpectrum P.Tensor, P.Tensor ⧸ I.asIdeal) :=
      { __ := P.residueDecomposition.toRingHom
        commutes' := fun r => P.residueDecomposition.commutes (r : ℚ_[p]) }
    change IsIntegral ℤ_[p] (e x) at hy
    exact (isIntegral_algHom_iff e P.residueDecomposition.injective).mp hy

def normalizationResidueMap : P.normalization →ₐ[ℤ_[p]]
    ∀ I : MaximalSpectrum P.Tensor, integralClosure ℤ_[p] (P.Tensor ⧸ I.asIdeal) where
  toFun x I := ⟨Ideal.Quotient.mk I.asIdeal x,
    IsIntegral.map_of_comp_eq (RingHom.id ℤ_[p]) (Ideal.Quotient.mk I.asIdeal)
      (RingHom.ext fun _ => rfl) x.2⟩
  map_one' := by funext I; exact Subtype.ext (map_one _)
  map_mul' x y := by funext I; exact Subtype.ext (map_mul _ _ _)
  map_zero' := by funext I; exact Subtype.ext (map_zero _)
  map_add' x y := by funext I; exact Subtype.ext (map_add _ _ _)
  commutes' r := by funext I; exact Subtype.ext rfl

theorem normalizationResidueMap_bijective : Function.Bijective P.normalizationResidueMap := by
  constructor
  · intro x y hxy
    refine Subtype.ext (P.eq_of_forall_residue_eq fun I => ?_)
    exact congrArg Subtype.val (congrFun hxy I)
  · intro y
    let b : ∀ I : MaximalSpectrum P.Tensor, P.Tensor ⧸ I.asIdeal := fun I => y I
    let x := P.residueDecomposition.symm b
    have hcoords (I : MaximalSpectrum P.Tensor) : Ideal.Quotient.mk I.asIdeal x = b I :=
      congrFun (P.residueDecomposition.apply_symm_apply b) I
    have hx : IsIntegral ℤ_[p] x := (P.isIntegral_iff_residue_integral x).mpr fun I => by
      rw [hcoords I]
      exact (y I).2
    refine ⟨⟨x, hx⟩, ?_⟩
    funext I
    exact Subtype.ext (hcoords I)

def normalizationDecomposition : P.normalization ≃ₐ[ℤ_[p]]
    ∀ I : MaximalSpectrum P.Tensor, integralClosure ℤ_[p] (P.Tensor ⧸ I.asIdeal) :=
  AlgEquiv.ofBijective P.normalizationResidueMap P.normalizationResidueMap_bijective

theorem normalizationDecomposition_apply (x : P.normalization) (I : MaximalSpectrum P.Tensor) :
    (P.normalizationDecomposition x I : P.Tensor ⧸ I.asIdeal) =
      Ideal.Quotient.mk I.asIdeal (x : P.Tensor) := rfl

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
