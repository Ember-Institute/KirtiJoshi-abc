/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/U2/CoreMap.lean
-/
import Solutions.Source_ReferenceIutCanLiftGaloisAction
import Solutions.Source_ReferenceIutCanLiftGaloisRamification
import Solutions.Source_ReferenceIutCanLiftRealization
import Solutions.Source_ReferenceIutCanLiftXDescent
import Mathlib.FieldTheory.Normal.Closure
import Solutions.Source_ReferenceIutCanLiftRamificationTransport

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open IntermediateField Ideal JoshiTeich.Act1Scene1
open JoshiTeich.Act1Scene1.AffineOrbicurvePresentation (Cover)
open JoshiTeich.Act1Scene1.FunctionFieldNormalization

private theorem cover_ramification_of_realization {Y Z : AffineOrbicurvePresentation ℂ}
    (ψ : Cover Z Y) (hZ : ∀ w : Ideal Z.A, w.IsMaximal → Z.mult w = 1)
    {F L : IntermediateField (rationalBase ℂ tΩ) Ωt} [IsDedekindDomain (coordRing tΩ F)]
    (hFL : F ≤ L) (eY : Y.A ≃ₐ[ℂ] coordRing tΩ F) (eZ : Z.A ≃ₐ[ℂ] coordRing tΩ L)
    (hψ : ∀ a, eZ (ψ.f a) = ringMap hFL (eY a))
    (w : Ideal (coordRing tΩ L)) (hw : w.IsMaximal) :
    (letI := ringMapAlgebra hFL; w.ramificationIdx (coordRing tΩ F)) =
      Y.mult ((w.comap (ringMap hFL)).comap eY) := by
  letI : w.IsPrime := hw.isPrime
  letI : w.IsMaximal := hw
  let q := w.comap eZ.toRingEquiv.toRingHom
  have hq : q.IsMaximal := Ideal.comap_isMaximal_of_equiv eZ.toRingEquiv
  have hcomp : (ringMap hFL).toRingHom.comp eY.toRingEquiv.toRingHom =
      eZ.toRingEquiv.toRingHom.comp ψ.f.toRingHom := RingHom.ext fun a => (hψ a).symm
  have hidx := (ramificationIdx_equiv_comp eY.toRingEquiv (ringMap hFL).toRingHom
    (ringMap_injective hFL) w).symm
  have htransport := ramificationIdx_congr hcomp w
  have hcomap : (w.comap (ringMap hFL).toRingHom).comap eY.toRingEquiv.toRingHom =
      q.comap ψ.f.toRingHom := by
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap]
  have hram := ψ.ramification q hq
  rw [hZ q hq, mul_one] at hram
  exact hidx.trans (htransport.trans
    ((ramificationIdx_comp_equiv ψ.f.toRingHom eZ.toRingEquiv w).trans
      (hram.trans (congrArg Y.mult hcomap.symm))))

private noncomputable def unramifiedNormalizationCover {Z : AffineOrbicurvePresentation ℂ}
    (hZ : ∀ v : Ideal Z.A, v.IsMaximal → Z.mult v = 1)
    {L M : IntermediateField (rationalBase ℂ tΩ) Ωt}
    [FiniteDimensional (rationalBase ℂ tΩ) M] [Algebra.IsSeparable (rationalBase ℂ tΩ) M]
    (eZ : Z.A ≃ₐ[ℂ] coordRing tΩ L) (hLM : L ≤ M)
    (he : ∀ w : Ideal (coordRing tΩ M), w.IsMaximal →
      (letI := ringMapAlgebra hLM; w.ramificationIdx (coordRing tΩ L)) = 1) :
    let T : AffineOrbicurvePresentation ℂ := {
      A := coordRing tΩ M
      isDedekindDomain := dedekindRing tΩ transcendental_tΩ M
      finiteType := finiteTypeRing tΩ transcendental_tΩ M
      not_isField := notFieldRing tΩ transcendental_tΩ M
      mult := fun _ => 1
      mult_pos := fun _ _ => Nat.one_pos
      finite_mult := by simp
    }
    Cover T Z := by
  intro T
  let f := (ringMap hLM).comp eZ.toAlgHom
  refine ⟨f, (ringMap_injective hLM).comp eZ.injective,
    RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ eZ.surjective)
      (ringMap_isIntegral hLM), ?_⟩
  intro w hw
  letI : w.IsMaximal := hw
  letI : w.IsPrime := hw.isPrime
  letI : FiniteDimensional (rationalBase ℂ tΩ) L :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hLM).toLinearMap
      (IntermediateField.inclusion hLM).injective
  letI : Algebra.IsSeparable (rationalBase ℂ tΩ) L :=
    Algebra.IsSeparable.of_algHom (F := rationalBase ℂ tΩ) (E := L) (E' := M)
      (IntermediateField.inclusion hLM)
  letI := dedekindRing tΩ transcendental_tΩ L
  have hq : (w.comap f).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f.toRingHom
      (RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ eZ.surjective)
        (ringMap_isIntegral hLM)) w
  change (letI := f.toRingHom.toAlgebra; w.ramificationIdx Z.A) * 1 = Z.mult (w.comap f)
  have hidx : (letI := f.toRingHom.toAlgebra; w.ramificationIdx Z.A) =
      (letI := ringMapAlgebra hLM;
        (w : Ideal (coordRing tΩ M)).ramificationIdx (coordRing tΩ L)) :=
    ramificationIdx_equiv_comp eZ.toRingEquiv (ringMap hLM).toRingHom (ringMap_injective hLM)
      (w : Ideal (coordRing tΩ M))
  calc
    _ = 1 * 1 := congrArg (· * 1) (hidx.trans (he w hw))
    _ = 1 := Nat.mul_one 1
    _ = _ := (hZ _ hq).symm

/-- An affine orbicurve cover of multiplicity one has an unramified Galois closure over its source.
The closure ring is fixed precisely over the coordinate ring of the original target. -/
theorem canLift27UnramifiedGaloisClosure : CanLift27UnramifiedGaloisClosure := by
  intro Z Y ψ hZ
  obtain ⟨F, L, hF, hL, hFL, eY, eZ, hψ⟩ := exists_realization ψ
  let N := IntermediateField.normalClosure (rationalBase ℂ tΩ) L Ωt
  letI : FiniteDimensional (rationalBase ℂ tΩ) F := hF
  letI : FiniteDimensional (rationalBase ℂ tΩ) L := hL
  letI : FiniteDimensional (rationalBase ℂ tΩ) N := inferInstance
  letI : IsGalois (rationalBase ℂ tΩ) N := by
    letI : Algebra.IsSeparable (rationalBase ℂ tΩ) N :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact IsGalois.mk
  let M := galoisClosure (N := N) F L
  have hLN : L ≤ N := IntermediateField.le_normalClosure L
  have hLM : L ≤ M := le_galoisClosure hLN
  have hFM : F ≤ M := hFL.trans hLM
  have hMN : M ≤ N := galoisClosure_le
  letI : FiniteDimensional (rationalBase ℂ tΩ) M :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hMN).toLinearMap
      (IntermediateField.inclusion hMN).injective
  letI : Algebra.IsSeparable (rationalBase ℂ tΩ) M :=
    Algebra.IsSeparable.of_algHom (F := rationalBase ℂ tΩ) (E := M) (E' := N)
      (IntermediateField.inclusion hMN)
  letI : Algebra.IsSeparable (rationalBase ℂ tΩ) F :=
    Algebra.IsSeparable.of_algHom (F := rationalBase ℂ tΩ) (E := F) (E' := N)
      (IntermediateField.inclusion (hFL.trans hLN))
  letI := dedekindRing tΩ transcendental_tΩ F
  let m : Ideal (coordRing tΩ F) → ℕ := fun q => Y.mult (q.comap eY)
  have hm (w : Ideal (coordRing tΩ L)) (hw : w.IsMaximal) :
      (letI := ringMapAlgebra hFL; w.ramificationIdx (coordRing tΩ F)) =
        m (w.comap (ringMap hFL)) :=
    cover_ramification_of_realization ψ hZ hFL eY eZ hψ w hw
  let γ := unramifiedNormalizationCover hZ eZ hLM
    (galoisClosure_ramificationIdx_eq_one transcendental_tΩ hFL hLN m hm)
  let G := galoisClosureAutomorphisms (N := N) (F := F) (L := L)
  refine ⟨_, γ, G, inferInstance, inferInstance, ?_⟩
  letI : Algebra Y.A (coordRing tΩ M) := (γ.f.comp ψ.f).toRingHom.toAlgebra
  letI : Algebra (coordRing tΩ F) (coordRing tΩ M) := ringMapAlgebra hFM
  letI : IsGaloisGroup G (coordRing tΩ F) (coordRing tΩ M) := galoisClosure_isGaloisGroup hFM
  refine IsGaloisGroup.of_ringEquiv (G := G) (A := coordRing tΩ F) (A' := Y.A)
    (B := coordRing tΩ M) eY.symm.toRingEquiv ?_
  intro a
  change ringMap hLM (eZ (ψ.f (eY.symm a))) = ringMap hFM a
  rw [hψ, AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Once automorphism invariance is known, the algebraic closure argument descends the
horizontal coordinate to every common cover target. -/
theorem canLift27ComplexXDescends_of_analytic (hfix : CanLift27ComplexAutomorphismsFixX) :
    CanLift27ComplexXDescends :=
  canLift27ComplexXDescends_of_automorphisms hfix canLift27UnramifiedGaloisClosure

end AbcAdaptation.Reference.Iut.Anabelian
