import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Etale.Locus
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.RingTheory.DualNumber

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Mathlib standard etale algebras and
uniqueness of maps to a square-zero extension for unramified algebras.
fidelity: computes the etale locus of a monic polynomial quotient as the
complement of its derivative. Necessity uses distinct infinitesimal lifts.
boundary: Scene1/Derived. The Weierstrass consumer supplies its actual polynomial.
-/

namespace JoshiTeich.Act1Scene1.AdjoinRootEtaleLocus

open Polynomial Algebra TrivSqZeroExt
open scoped Classical DualNumber
noncomputable section
variable {R : Type*} [CommRing R] (f : R[X])

theorem etale_away_derivative (hf : f.Monic) :
    Algebra.Etale R (Localization.Away (AdjoinRoot.mk f f.derivative)) := by
  let P : StandardEtalePair R := ⟨f, hf, f.derivative, 1, 0, 1, by simp⟩
  exact Algebra.Etale.of_equiv P.equivAwayAdjoinRoot

theorem isEtaleAt_of_derivative_not_mem (hf : f.Monic)
    (q : Ideal (AdjoinRoot f)) [q.IsPrime] (hq : AdjoinRoot.mk f f.derivative ∉ q) :
    Algebra.IsEtaleAt R q := by
  have := etale_away_derivative f hf
  exact (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr
    (etale_away_derivative f hf))
      (show (⟨q, inferInstance⟩ : PrimeSpectrum (AdjoinRoot f)) ∈
        PrimeSpectrum.basicOpen (AdjoinRoot.mk f f.derivative) from hq)

/-- A double root has two distinct lifts to the dual numbers over its residue field. -/
theorem derivative_not_mem_of_isUnramifiedAt
    (q : Ideal (AdjoinRoot f)) [q.IsPrime] [Algebra.IsUnramifiedAt R q] :
    AdjoinRoot.mk f f.derivative ∉ q := by
  intro hd
  let K := q.ResidueField
  let D := DualNumber K
  let φ : AdjoinRoot f →ₐ[R] K := IsScalarTower.toAlgHom R (AdjoinRoot f) K
  let π : D →ₐ[R] K := fstHom R K K
  let g₀ : AdjoinRoot f →ₐ[R] D := (inlAlgHom R K K).comp φ
  have hroot : aeval (g₀ (AdjoinRoot.root f)) f = 0 := by
    rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  have hder : aeval (g₀ (AdjoinRoot.root f)) f.derivative = 0 := by
    rw [aeval_algHom_apply, AdjoinRoot.aeval_eq]
    change inl (algebraMap (AdjoinRoot f) K (AdjoinRoot.mk f f.derivative)) = 0
    rw [Ideal.algebraMap_residueField_eq_zero.mpr hd, inl_zero]
  let g₁ : AdjoinRoot f →ₐ[R] D := AdjoinRoot.liftAlgHom f (Algebra.ofId R D)
    (g₀ (AdjoinRoot.root f) + DualNumber.eps) (by
      change aeval _ f = 0
      rw [aeval_add_of_sq_eq_zero _ _ _ (by
        rw [pow_two]; exact DualNumber.eps_mul_eps), hroot, hder, zero_mul, add_zero])
  have hπ₀ : π.comp g₀ = φ := by ext; rfl
  have hπ₁ : π.comp g₁ = φ := by
    apply AdjoinRoot.algHom_ext
    change π (g₁ (AdjoinRoot.root f)) = φ (AdjoinRoot.root f)
    rw [show g₁ (AdjoinRoot.root f) = g₀ (AdjoinRoot.root f) + DualNumber.eps from
      AdjoinRoot.liftAlgHom_root _ _ _ _]
    change φ (AdjoinRoot.root f) + 0 = φ (AdjoinRoot.root f)
    exact add_zero _
  have hunit (g : AdjoinRoot f →ₐ[R] D) (hg : π.comp g = φ)
      (s : q.primeCompl) : IsUnit (g s) := by
    rw [isUnit_iff_isUnit_fst, isUnit_iff_ne_zero]
    change π (g s) ≠ 0
    rw [← AlgHom.comp_apply, hg]
    exact fun h => s.2 (Ideal.algebraMap_residueField_eq_zero.mp h)
  let l₀ : Localization.AtPrime q →ₐ[R] D := IsLocalization.liftAlgHom (hunit g₀ hπ₀)
  let l₁ : Localization.AtPrime q →ₐ[R] D := IsLocalization.liftAlgHom (hunit g₁ hπ₁)
  have heq : π.toRingHom.comp l₀.toRingHom = π.toRingHom.comp l₁.toRingHom := by
    apply IsLocalization.ringHom_ext q.primeCompl
    apply RingHom.ext
    intro a
    change π (l₀ (algebraMap _ _ a)) = π (l₁ (algebraMap _ _ a))
    simp only [l₀, l₁, IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq]
    exact (AlgHom.congr_fun hπ₀ a).trans (AlgHom.congr_fun hπ₁ a).symm
  have hl : l₀ = l₁ := Algebra.FormallyUnramified.lift_unique_of_ringHom
    π.toRingHom ⟨2, TrivSqZeroExt.kerIdeal_sq K K⟩ l₀ l₁ heq
  have hr := AlgHom.congr_fun hl (algebraMap (AdjoinRoot f) (Localization.AtPrime q) (AdjoinRoot.root f))
  simp only [l₀, l₁, IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq] at hr
  change g₀ (AdjoinRoot.root f) = g₁ (AdjoinRoot.root f) at hr
  rw [show g₁ (AdjoinRoot.root f) = g₀ (AdjoinRoot.root f) + DualNumber.eps from
    AdjoinRoot.liftAlgHom_root _ _ _ _] at hr
  have hs := congrArg TrivSqZeroExt.snd hr
  change snd (g₀ (AdjoinRoot.root f)) = snd (g₀ (AdjoinRoot.root f)) + 1 at hs
  exact one_ne_zero (add_left_cancel (hs.symm.trans (add_zero _).symm))

theorem isEtaleAt_iff_derivative_not_mem (hf : f.Monic)
    (q : Ideal (AdjoinRoot f)) [q.IsPrime] :
    Algebra.IsEtaleAt R q ↔ AdjoinRoot.mk f f.derivative ∉ q := by
  constructor
  · intro h
    have := h
    exact derivative_not_mem_of_isUnramifiedAt f q
  · exact isEtaleAt_of_derivative_not_mem f hf q

end
end JoshiTeich.Act1Scene1.AdjoinRootEtaleLocus
