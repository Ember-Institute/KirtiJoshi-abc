import Solutions.Source_ReferenceIutCanLiftBranchMultiplicity
import Solutions.Source_ReferenceIutCanLiftPolynomialRamification
import Solutions.Source_ReferenceIutCanLiftPolynomialRigidity
import Solutions.Source_ReferenceIutCanLiftComplex

/-!
This applies the polynomial rigidity calculation from `OrbicurveCores/U2/HemiUnique.lean`
and `OrbicurveCores/U2/Assembly.lean` at revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
to self-covers of the actual level-one signed normalization.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve Polynomial JoshiTeich.Act1Scene1
open JoshiTeich.Act1Scene1.AffineOrbicurvePresentation
open JoshiTeich.ReferenceIut.Anabelian.Genuine
open scoped Classical

noncomputable section

variable (E : WeierstrassCurve ℂ) [E.IsElliptic]

local notation "H" => normalizationPresentation E 1 ⊥ true

private theorem signed_mult_at_polynomialPoint (w : ℂ) :
    (H).mult ((polynomialPointIdeal w).comap (signedBasePolynomialAlgEquiv E).symm.toRingEquiv) =
      hemiMultiplicity (E₂ E) w := by
  let e := signedBasePolynomialAlgEquiv E
  letI : (polynomialPointIdeal w).IsMaximal := polynomialPointIdeal_isMaximal w
  have hw : ((polynomialPointIdeal w).comap e.symm.toRingEquiv).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective e.symm.toRingHom e.symm.surjective
  have hroot : signedBasePolynomialAlgEquiv E E.twoTorsionPolynomial.toPoly ∈
      (polynomialPointIdeal w).comap e.symm.toRingEquiv ↔ w ∈ E₂ E := by
    change e.symm (e (tq E)) ∈ polynomialPointIdeal w ↔ w ∈ E₂ E
    rw [e.symm_apply_apply, E₂, Multiset.mem_toFinset, mem_roots tq_ne_zero,
      polynomialPointIdeal, Ideal.mem_span_singleton, dvd_iff_isRoot]
  refine (normalizationPresentation_signed_mult_eq_branch E _ hw).trans ?_
  unfold hemiMultiplicity
  by_cases h : w ∈ E₂ E
  · rw [if_pos (hroot.mpr h), if_pos h]
  · rw [if_neg (fun hm => h (hroot.mp hm)), if_neg h]

private theorem signed_cover_polynomial_ramification (f : Cover H H) {p : ℂ[X]}
    (hinj : Function.Injective (aeval (R := ℂ) p))
    (hcomm : ∀ a : ℂ[X], f.f (signedBasePolynomialAlgEquiv E a) =
      signedBasePolynomialAlgEquiv E (aeval (R := ℂ) p a)) (w : ℂ) :
    polynomialRamificationIdx p w * hemiMultiplicity (E₂ E) w =
      hemiMultiplicity (E₂ E) (p.eval w) := by
  let e : ℂ[X] ≃ₐ[ℂ] (H).A := signedBasePolynomialAlgEquiv E
  letI : Algebra ℂ[X] ℂ[X] := (aeval (R := ℂ) p).toRingHom.toAlgebra
  letI : Algebra (H).A (H).A := f.f.toRingHom.toAlgebra
  let q := (polynomialPointIdeal w).comap e.symm.toRingEquiv
  let v := (polynomialPointIdeal (p.eval w)).comap e.symm.toRingEquiv
  letI : (polynomialPointIdeal w).IsMaximal := polynomialPointIdeal_isMaximal w
  letI : (polynomialPointIdeal (p.eval w)).IsMaximal := polynomialPointIdeal_isMaximal _
  have hq : q.IsMaximal := Ideal.comap_isMaximal_of_surjective e.symm.toRingHom e.symm.surjective
  have hv : v.IsMaximal := Ideal.comap_isMaximal_of_surjective e.symm.toRingHom e.symm.surjective
  letI : q.IsPrime := hq.isPrime
  have hcontract : q.comap f.f.toRingHom = v := by
    ext a
    obtain ⟨b, rfl⟩ := e.surjective a
    change e.symm (f.f (e b)) ∈ polynomialPointIdeal w ↔
      e.symm (e b) ∈ polynomialPointIdeal (p.eval w)
    rw [show f.f (e b) = e (aeval (R := ℂ) p b) from hcomm b]
    simp only [AlgEquiv.symm_apply_apply]
    change b ∈ (polynomialPointIdeal w).comap (aeval (R := ℂ) p).toRingHom ↔
      b ∈ polynomialPointIdeal (p.eval w)
    rw [polynomialPointIdeal_comap_aeval]
  letI : q.LiesOver v := ⟨hcontract.symm⟩
  have hsq (a : ℂ[X]) : e.toRingEquiv (algebraMap ℂ[X] ℂ[X] a) =
      algebraMap (H).A (H).A (e.toRingEquiv a) := (hcomm a).symm
  have hv₀ : v ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hv (H).not_isField
  have hvmap : v.map (algebraMap (H).A (H).A) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective f.injective).not.mpr hv₀
  have hqcomap : q.comap e.toRingEquiv = polynomialPointIdeal w := by
    ext a
    change e.symm (e a) ∈ polynomialPointIdeal w ↔ a ∈ polynomialPointIdeal w
    rw [e.symm_apply_apply]
  have hidx := RamificationEquivSquare.ramificationIdx_eq e.toRingEquiv e.toRingEquiv hsq v q hvmap
  rw [hqcomap] at hidx
  have hcover := f.ramification q hq
  change q.ramificationIdx (H).A * (H).mult q = (H).mult (q.comap f.f.toRingHom) at hcover
  rw [hcontract] at hcover
  have hsource := signed_mult_at_polynomialPoint E w
  have htarget := signed_mult_at_polynomialPoint E (p.eval w)
  change (H).mult q = _ at hsource
  change (H).mult v = _ at htarget
  rw [hsource, htarget, ← hidx] at hcover
  exact (congrArg (fun n => n * hemiMultiplicity (E₂ E) w)
    (ramificationIdx_aeval_eq_polynomialRamificationIdx hinj w)).symm.trans hcover

/-- Every self-cover of the punctured sign quotient is the identity away from the two
`j`-invariants that allow a nontrivial affine symmetry of the two-torsion roots. -/
theorem canLift27ComplexHemiRigid : CanLift27ComplexHemiRigid := by
  intro E _ hj₀ hj₁₇₂₈ f
  let e : ℂ[X] ≃ₐ[ℂ] (normalizationPresentation E 1 ⊥ true).A := signedBasePolynomialAlgEquiv E
  let p := e.symm (f.f (e X))
  have hf : f.f.comp e.toAlgHom = e.toAlgHom.comp (aeval (R := ℂ) p) := by
    apply Polynomial.algHom_ext
    change f.f (e X) = e (aeval (R := ℂ) p X)
    rw [aeval_X]
    exact (e.apply_symm_apply _).symm
  have hcomm (a : ℂ[X]) : f.f (e a) = e (aeval (R := ℂ) p a) := AlgHom.congr_fun hf a
  have hinj : Function.Injective (aeval (R := ℂ) p) := by
    intro a b hab
    apply e.injective
    apply f.injective
    rw [hcomm a, hcomm b, hab]
  have hp : 0 < p.natDegree := by
    by_contra h
    have hpC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos h)
    have hz : aeval (R := ℂ) p (X - C (p.coeff 0)) = aeval (R := ℂ) p 0 := by
      rw [map_sub, aeval_X, aeval_C, algebraMap_eq, ← hpC, sub_self, map_zero]
    exact X_sub_C_ne_zero _ (hinj hz)
  rcases hemi_poly_unique hp (signed_cover_polynomial_ramification E f hinj hcomm) with hX | h | h
  · apply Cover.ext_f
    apply AlgHom.ext
    intro a
    obtain ⟨b, rfl⟩ := e.surjective a
    change f.f (e b) = e b
    rw [hcomm, hX, ← comp_eq_aeval, comp_X]
  · exact (hj₀ h).elim
  · exact (hj₁₇₂₈ h).elim

end

end AbcAdaptation.Reference.Iut.Anabelian
