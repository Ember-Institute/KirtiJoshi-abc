/-
Source: Pi1/Orbicurve/EmbedComplex.lean (`nonempty_ringHom_complex`) and
Pi1/Orbicurve/LefschetzMain.lean (`canLift27_of_complex`) at revision
ca7def953193f861a462aa0831eec8f0a31ff69f, Apache-2.0.
Original author: Christian Merten and the pi1 contributors.
-/
import Solutions.Source_ReferenceIutCanLiftPresentation
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.FieldTheory.AlgebraicClosure

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open Cardinal WeierstrassCurve
open JoshiTeich.Act1Scene1.AffineOrbicurvePresentation (IsCoreOf)
open JoshiTeich.ReferenceIut.Anabelian.Genuine (normalizationPresentation)

private theorem nonempty_ringHom_complex (L : Type) [Field L] [CharZero L] [Countable L] :
    Nonempty (L →+* ℂ) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ L
  obtain ⟨b, hb⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hbcard : #b = 𝔠 := by
    have h := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' (R := ℚ)
      ((↑) : b → ℂ) hb (le_of_eq Cardinal.mkRat) (by rw [Cardinal.mk_complex]; exact
        Cardinal.aleph0_lt_continuum)
    rw [← h, Cardinal.mk_complex]
  have hsb : #s ≤ #b := by
    rw [hbcard]
    exact Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum
  obtain ⟨e⟩ := hsb
  let x : s → L := (↑)
  let y : s → ℂ := fun i => (e i : ℂ)
  have hy : AlgebraicIndependent ℚ y := hb.1.comp e e.injective
  let g : MvPolynomial s ℚ →+* ℂ := (MvPolynomial.aeval (R := ℚ) y).toRingHom
  have hginj : Function.Injective g := algebraicIndependent_iff_injective_aeval.mp hy
  let R := Algebra.adjoin ℚ (Set.range x)
  let φ : R →+* ℂ := g.comp hs.1.aevalEquiv.symm.toRingEquiv.toRingHom
  have hφ : Function.Injective φ := hginj.comp hs.1.aevalEquiv.symm.injective
  letI : Algebra R ℂ := φ.toAlgebra
  letI : Algebra.IsAlgebraic R L := hs.isAlgebraic
  letI : Module.IsTorsionFree R ℂ := Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  letI : Module.IsTorsionFree R L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Subtype.val_injective
  exact ⟨(IsAlgClosed.lift (M := ℂ) (R := R) (S := L)).toRingHom⟩

private theorem nonexceptionalJ_map_iff {k K : Type} [Field k] [Field K] [CharZero k]
    [CharZero K] (f : k →+* K) (E : WeierstrassCurve k) [E.IsElliptic] :
    (∀ c ∈ canLiftExceptionalJ, (E.map f).j ≠ (c : K)) ↔
      (∀ c ∈ canLiftExceptionalJ, E.j ≠ (c : k)) := by
  constructor
  · intro h c hc hj
    apply h c hc
    rw [WeierstrassCurve.map_j, hj, map_ratCast]
  · intro h c hc hj
    rw [WeierstrassCurve.map_j, ← map_ratCast f] at hj
    exact h c hc (f.injective hj)

private abbrev signedNormalizationIsCore {k : Type} [Field k] [CharZero k]
    (E : WeierstrassCurve k) [E.IsElliptic] : Prop :=
  IsCoreOf (normalizationPresentation E 1 ⊥ false) (normalizationPresentation E 1 ⊥ true)

/-- The Lefschetz assembly uses descent along an embedding and determination by countable
algebraically closed subfields. These are the two geometric descent steps in the source. -/
theorem canLift27_of_complex_of_descent (hcomplex : CanLift27Complex)
    (hdescend : ∀ {k K : Type} [Field k] [Field K] [CharZero k] [CharZero K]
      (f : k →+* K) (E : WeierstrassCurve k) [E.IsElliptic],
        signedNormalizationIsCore (E.map f) → signedNormalizationIsCore E)
    (hsubfield : ∀ {K : Type} [Field K] [CharZero K] [IsAlgClosed K]
      (E : WeierstrassCurve K) [E.IsElliptic],
        (∀ (L : Subfield K) [IsAlgClosed L] [Countable L] (W : WeierstrassCurve L)
          [W.IsElliptic], W.map (algebraMap L K) = E → signedNormalizationIsCore W) →
        signedNormalizationIsCore E) : CanLift27.{0} := by
  intro k _ _ E _ hj
  let K := AlgebraicClosure k
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let f := algebraMap k K
  have hjK := (nonexceptionalJ_map_iff f E).mpr hj
  refine hdescend f E (hsubfield (E.map f) ?_)
  intro L _ _ W _ hW
  obtain ⟨ι⟩ := nonempty_ringHom_complex L
  have hjL : ∀ c ∈ canLiftExceptionalJ, W.j ≠ (c : L) := by
    apply (nonexceptionalJ_map_iff (algebraMap L K) W).mp
    simpa only [hW] using hjK
  exact hdescend ι W (hcomplex (W.map ι) ((nonexceptionalJ_map_iff ι W).mpr hjL))

end AbcAdaptation.Reference.Iut.Anabelian
