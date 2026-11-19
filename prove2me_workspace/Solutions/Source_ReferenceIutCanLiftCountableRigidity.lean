/-
Source: Pi1/Orbicurve/LefschetzMain.lean (`coreStar_of_subfields`) at revision
ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.
-/
import Solutions.Source_ReferenceIutCanLiftCountableCoverField
import Solutions.Source_ReferenceIutCanLiftCoreStar

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open Polynomial WeierstrassCurve
open JoshiTeich.Act1Scene1.AffineOrbicurvePresentation (IsCoreOf)
open JoshiTeich.Act1Scene1.FunctionFieldNormalization
open JoshiTeich.ReferenceIut.Anabelian.Genuine (ιF xF yF normalizationPresentation)

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]

/-- Rigidity over the countable models of `E` implies rigidity for the same Weierstrass
coordinates in `Ω`. Each tested cover selects one model containing both relevant coordinates. -/
theorem quadraticCoverRigidity_of_countable_models [IsAlgClosed K] [CharZero K] [IsAlgClosed Ω]
    (E : WeierstrassCurve K) [E.IsElliptic] {t y : Ω} (ht : Transcendental K t)
    (hy : y ^ 2 + weierstrassQuadraticB E t * y = weierstrassQuadraticC E t)
    (H : ∀ (k : Subfield K) [IsAlgClosed k] [Countable k] (W : WeierstrassCurve k)
      [W.IsElliptic], W.map (algebraMap k K) = E → QuadraticCoverRigidity k t y) :
    QuadraticCoverRigidity K t y := by
  intro L hLdim hL het g _ hgIntegral hgRamification
  letI : FiniteDimensional (rationalBase K t) L := hLdim
  let s : L := (g (constantExtensionLineEquiv ht X) : coordRing t L)
  have hyL : y ∈ L := hL (IntermediateField.mem_adjoin_simple_self (rationalBase K t) y)
  obtain ⟨k, hkClosed, hkCountable, W, hWell, hWE, F, hFdim, hFL, hLF, hsF, hyF⟩ :=
    exists_countable_cover_field E t L s ⟨y, hyL⟩
  letI : IsAlgClosed k := hkClosed
  letI : Countable k := hkCountable
  letI : W.IsElliptic := hWell
  letI : FiniteDimensional (rationalBase k t) F := hFdim
  have hb : weierstrassQuadraticB E t ∈ rationalBase k t := by
    rw [← hWE, weierstrassQuadraticB_map]
    exact weierstrassQuadraticB_mem W t
  have hc : weierstrassQuadraticC E t ∈ rationalBase k t := by
    rw [← hWE, weierstrassQuadraticC_map]
    exact weierstrassQuadraticC_mem W t
  exact quadraticCoverMap_eq_of_descended ht hb hc hy (H k W hWE) hFL hLF hyF hL het g
    hgIntegral hgRamification hsF

/-- Core uniqueness over all countable algebraically closed models implies core uniqueness
on the same curve over the given algebraically closed field. -/
theorem normalizationCoreStar_of_countable_models [IsAlgClosed K] [CharZero K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : ∀ (k : Subfield K) [IsAlgClosed k] [Countable k] (W : WeierstrassCurve k)
      [W.IsElliptic], W.map (algebraMap k K) = E → NormalizationCoreStar W) :
    NormalizationCoreStar E := by
  let j := ιF E
  let t := j (xF E)
  let y := j (yF E)
  have ht : Transcendental K t := transcendental_functionField_x E j
  have hy : y ^ 2 + weierstrassQuadraticB E t * y = weierstrassQuadraticC E t :=
    functionField_quadratic E j
  apply normalizationCoreStar_of_quadraticCoverRigidity E j
  refine quadraticCoverRigidity_of_countable_models E ht hy ?_
  intro k _ _ W _ hWE
  letI : Algebra k (JoshiTeich.ReferenceIut.Anabelian.Genuine.Ω E) := Algebra.ofSubsemiring k
  have htk : Transcendental k t := transcendental_of_constantExtension ht
  have hyk : y ^ 2 + weierstrassQuadraticB W t * y = weierstrassQuadraticC W t := by
    rw [← weierstrassQuadraticB_map (K := K) W t, ← weierstrassQuadraticC_map (K := K) W t, hWE]
    exact hy
  obtain ⟨i, hx, hiy⟩ := exists_functionField_embedding_of_quadratic W htk hyk
  change QuadraticCoverRigidity k t y
  rw [← hx, ← hiy]
  exact quadraticCoverRigidity_of_normalizationCoreStar W i (H k W hWE)

/-- If the actual signed normalization is a core on every countable model, then it is a core
on the given curve over the algebraically closed field. -/
theorem normalizationIsCore_of_countable_models [IsAlgClosed K] [CharZero K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (H : ∀ (k : Subfield K) [IsAlgClosed k] [Countable k] (W : WeierstrassCurve k)
      [W.IsElliptic], W.map (algebraMap k K) = E →
        IsCoreOf (normalizationPresentation W 1 ⊥ false) (normalizationPresentation W 1 ⊥ true)) :
    IsCoreOf (normalizationPresentation E 1 ⊥ false) (normalizationPresentation E 1 ⊥ true) := by
  apply normalizationIsCore_of_normalizationCoreStar E
  apply normalizationCoreStar_of_countable_models E
  intro k _ _ W _ hWE
  exact normalizationCoreStar_of_isCoreOf W (H k W hWE)

end

end AbcAdaptation.Reference.Iut.Anabelian
