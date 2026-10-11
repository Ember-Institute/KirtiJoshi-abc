/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/Existence.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `a36b42b9a221e1baaf434bb76c85b3a0dfbf33a7`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: adapts `ModEllRepData`, `globalData`, and `primeData` to the
complete odd support. Finite bounds supply the elementary prime conditions.
The mod representation and its SL2 image condition remain explicit inputs.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaLargePrimeSupport
import Mathlib.Data.Nat.Prime.Infinite

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField WeierstrassCurve TateCurvesTheta
open scoped Classical

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-MAXIMAL-PRIME-DATA
source: `refer/iut/Iut/Concrete/Existence.lean`, `ModEllRepData`,
`globalData`, and `primeData`; the full-support Tate parameters and S1.203;
mathlib `Nat.exists_infinite_primes`.
fidelity: constructs global and admissible-prime data on the complete odd
support of the given curve. The bound excludes residue characteristics,
Tate orders, and the relative field degree. Arbitrarily large primes meet
these elementary conditions. A genuine mod representation with SL2 in its
image is still required. Orbicurve and local theta data are not constructed.
boundary: Scene1/Derived
-/

/-- The representation input fixes the action on actual elliptic torsion. -/
structure IutCurveModEllRepData
    (F : Type u) [Field F] [NumberField F]
    (E : WeierstrassCurve F) [E.IsElliptic]
    (Fbar : Type u) [Field Fbar] [Algebra F Fbar] (ell : ℕ) : Type u where
  torsionBasis :
    AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell ≃+
      (Fin 2 → ZMod ell)
  rep : (Fbar ≃ₐ[F] Fbar) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod ell)
  rep_spec : ∀ (σ : Fbar ≃ₐ[F] Fbar)
    (P : AddSubgroup.torsionBy (Affine.Point (Affine.baseChange E Fbar)) ell),
    torsionBasis ⟨JoshiTeich.ReferenceIut.galPointMap F E Fbar σ P.1,
        JoshiTeich.ReferenceIut.galPointMap_torsionBy F E Fbar σ P.2⟩ =
      (rep σ : Matrix (Fin 2) (Fin 2) (ZMod ell)).mulVec (torsionBasis P)
  ker_isOpen : IsOpen (rep.ker : Set (Fbar ≃ₐ[F] Fbar))

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

/-- A finite upper bound for the canonical Tate orders on the full support. -/
def iutInitialThetaOddSupportQOrderBound : ℕ :=
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  B.badFinset.attach.sup B.qOrder

theorem iutInitialThetaOddSupportQOrder_le_bound
    (w : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
    (iutInitialThetaOddSupportBaseQPilotSource D).qOrder w ≤
      iutInitialThetaOddSupportQOrderBound D := by
  exact Finset.le_sup (Finset.mem_attach _ w)

/-- This bound is independent of the candidate prime. -/
def iutInitialThetaElementaryPrimeBound : ℕ :=
  max 6 (max (iutMultiplicativeResidueBound D.E)
    (max (Module.finrank ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) D.F)
      (iutInitialThetaOddSupportQOrderBound D)))

theorem iutInitialThetaElementaryPrimeBound_spec :
    6 ≤ iutInitialThetaElementaryPrimeBound D ∧
    iutMultiplicativeResidueBound D.E ≤ iutInitialThetaElementaryPrimeBound D ∧
    Module.finrank ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) D.F ≤
      iutInitialThetaElementaryPrimeBound D ∧
    iutInitialThetaOddSupportQOrderBound D ≤ iutInitialThetaElementaryPrimeBound D := by
  unfold iutInitialThetaElementaryPrimeBound
  refine ⟨le_max_left _ _, ?_, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Euclid's theorem supplies primes beyond any caller's threshold and the curve bound. -/
theorem iutInitialTheta_exists_largeElementaryPrime (n : ℕ) :
    ∃ ell : ℕ, ell.Prime ∧ n < ell ∧
      iutInitialThetaElementaryPrimeBound D < ell := by
  obtain ⟨ell, hle, hp⟩ :=
    Nat.exists_infinite_primes (max n (iutInitialThetaElementaryPrimeBound D) + 1)
  exact ⟨ell, hp, by omega, by omega⟩

theorem iutInitialThetaOddSupportQOrder_coprime_of_largePrime
    {ell : ℕ} (hp : ell.Prime)
    (hLarge : iutInitialThetaElementaryPrimeBound D < ell)
    (w : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
    Nat.Coprime ell ((iutInitialThetaOddSupportBaseQPilotSource D).qOrder w) := by
  apply Nat.coprime_of_lt_prime
    ((iutInitialThetaOddSupportBaseQPilotSource D).qOrder_pos w).ne'
  · exact (iutInitialThetaOddSupportQOrder_le_bound D w).trans_lt
      ((iutInitialThetaElementaryPrimeBound_spec D).2.2.2.trans_lt hLarge)
  · exact hp

theorem iutInitialThetaModSupport_residueChar_coprime_of_largePrime
    {ell : ℕ} (hp : ell.Prime)
    (hLarge : iutInitialThetaElementaryPrimeBound D < ell)
    (v : FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
    (hv : v ∈ IutOddMultiplicativeModSupport D) :
    Nat.Coprime ell (Arithmetic.residueChar v) := by
  obtain ⟨w, hwv⟩ := hv.2.1
  have hw := hv.2.2 w hwv
  have hle := iutMultiplicative_residueChar_le_bound D.E w hw
  rw [Arithmetic.residueChar_eq_of_liesOver hwv] at hle
  exact Nat.coprime_of_lt_prime (Arithmetic.residueChar_prime v).ne_zero
    (hle.trans_lt ((iutInitialThetaElementaryPrimeBound_spec D).2.1.trans_lt hLarge)) hp

/-- The original nonempty bad locus supplies nonemptiness of the maximal locus. -/
def iutInitialThetaMaximalGlobalData :
    JoshiTeich.ReferenceIut.IsInitialThetaGlobalData D.F D.E D.Fbar
      (IutOddMultiplicativeModSupport D) where
  sqrt_neg_one := D.global.sqrt_neg_one
  stable_reduction := D.global.stable_reduction
  six_torsion_rational := D.global.six_torsion_rational
  bad_nonempty := by
    obtain ⟨v, hv⟩ := D.global.bad_nonempty
    exact ⟨v, iutInitialThetaVBad_subset_oddMultiplicativeModSupport D hv⟩
  bad_odd _ hv := hv.1
  bad_multiplicative _ hv := hv.2.2

/-- The canonical completion uniformizer also satisfies the Tate library contract. -/
private theorem iutMaximal_completionUniformizer_isUniformizer
    (w : FinitePlace D.F) :
    IsUniformizer (Arithmetic.completionUniformizer w) := by
  have h := Arithmetic.completionUniformizer_isCompletionUniformizer w
  exact ⟨h.ne_zero, h.norm_lt_one, h.generates⟩

private theorem iutMaximal_canonicalOrder_eq_qOrder
    (w : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
    ((iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D w.1
      ((iutInitialThetaOddSupportBaseQPilotSource D).mem_badPlaces w)).toOrdered
      (iutMaximal_completionUniformizer_isUniformizer D w.1)).orderNat =
      (iutInitialThetaOddSupportBaseQPilotSource D).qOrder w := by
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let t := iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D w.1 (B.mem_badPlaces w)
  have hnorm : ‖B.tateParameter w‖ = ‖Arithmetic.completionUniformizer w.1‖ ^
      (t.toOrdered (iutMaximal_completionUniformizer_isUniformizer D w.1)).orderNat :=
    t.norm_q_eq_pow_orderNat (iutMaximal_completionUniformizer_isUniformizer D w.1)
  exact (iutCompletionQOrder_eq_of_norm_eq_uniformizer_pow w.1 (B.tateParameter w)
    (B.tateParameter_ne_zero w) (B.tateParameter_norm_lt_one w)
    (Arithmetic.completionUniformizer w.1)
    (Arithmetic.completionUniformizer_isCompletionUniformizer w.1) _ hnorm).symm

/-- Construct admissible-prime data on the maximal support from the genuine representation. -/
def iutInitialThetaMaximalPrimeData
    {ell : ℕ} (hp : ell.Prime)
    (hLarge : iutInitialThetaElementaryPrimeBound D < ell)
    (R : IutCurveModEllRepData D.F D.E D.Fbar ell)
    (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ell), A.toGL ∈ R.rep.range) :
    JoshiTeich.ReferenceIut.AdmissiblePrimeData D.F D.E D.Fbar
      (IutOddMultiplicativeModSupport D) := by
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  have memFull (w : FinitePlace D.F)
      (hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E
        (IutOddMultiplicativeModSupport D)) : w ∈ IutOddMultiplicativeSupport D :=
    (Set.ext_iff.mp (iutOddMultiplicativeSupport_eq_badPlacesOver_modSupport D) w).mpr hw
  have memFinset (w : FinitePlace D.F)
      (hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E
        (IutOddMultiplicativeModSupport D)) : w ∈ B.badFinset :=
    (Set.ext_iff.mp B.badFinset_spec w).mpr (memFull w hw)
  refine
    { ℓ := ell
      ℓ_prime := hp
      five_le := by have := (iutInitialThetaElementaryPrimeBound_spec D).1; omega
      torsionBasis := R.torsionBasis
      rep := R.rep
      rep_spec := R.rep_spec
      sl_le_range := hsl
      ker_isOpen := R.ker_isOpen
      galois_deg_prime := ?_
      residueChar_coprime := iutInitialThetaModSupport_residueChar_coprime_of_largePrime
        D hp hLarge
      tate := fun w hw => iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D w
        (memFull w hw)
      tateJ_eq := fun w hw =>
        iutInitialThetaOddSupportBaseTateParameterAtCurvePlace_tateJ_eq D w (memFull w hw)
      unif := fun w _ => Arithmetic.completionUniformizer w
      unif_isUniformizer := fun w _ => iutMaximal_completionUniformizer_isUniformizer D w
      q_order_coprime := ?_ }
  · refine ⟨D.prime.galois_deg_prime.1, ?_⟩
    exact (Nat.coprime_of_lt_prime (Module.finrank_pos.ne')
      ((iutInitialThetaElementaryPrimeBound_spec D).2.2.1.trans_lt hLarge) hp).symm
  · intro w hw
    change Nat.Coprime ell
      ((iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D w (memFull w hw)).toOrdered
        (iutMaximal_completionUniformizer_isUniformizer D w)).orderNat
    rw [iutMaximal_canonicalOrder_eq_qOrder D ⟨w, memFinset w hw⟩]
    exact iutInitialThetaOddSupportQOrder_coprime_of_largePrime D hp hLarge _

end

end JoshiTeich.Act1Scene1
