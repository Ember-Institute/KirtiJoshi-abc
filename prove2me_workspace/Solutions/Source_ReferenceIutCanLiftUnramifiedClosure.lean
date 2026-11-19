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
open scoped IntermediateField.algebraAdjoinAdjoin

universe u

variable {k : Type u} [Field k]

local notation "Ω" => ratFuncClosure k
local notation "t" => ratFuncClosureParameter k
local notation "K₀" => rationalBase k t

private theorem cover_ramification_of_realization {Y Z : AffineOrbicurvePresentation k}
    (ψ : Cover Z Y) (hZ : ∀ w : Ideal Z.A, w.IsMaximal → Z.mult w = 1)
    {F L : IntermediateField K₀ Ω} [IsDedekindDomain (coordRing t F)]
    (hFL : F ≤ L) (eY : Y.A ≃ₐ[k] coordRing t F) (eZ : Z.A ≃ₐ[k] coordRing t L)
    (hψ : ∀ a, eZ (ψ.f a) = ringMap hFL (eY a))
    (w : Ideal (coordRing t L)) (hw : w.IsMaximal) :
    (letI := ringMapAlgebra hFL; w.ramificationIdx (coordRing t F)) =
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

private noncomputable def unramifiedNormalizationCover {Z : AffineOrbicurvePresentation k}
    (hZ : ∀ v : Ideal Z.A, v.IsMaximal → Z.mult v = 1)
    {L M : IntermediateField K₀ Ω}
    [FiniteDimensional K₀ M] [Algebra.IsSeparable K₀ M]
    (eZ : Z.A ≃ₐ[k] coordRing t L) (hLM : L ≤ M)
    (he : ∀ w : Ideal (coordRing t M), w.IsMaximal →
      (letI := ringMapAlgebra hLM; w.ramificationIdx (coordRing t L)) = 1) :
    let T : AffineOrbicurvePresentation k := {
      A := coordRing t M
      isDedekindDomain := dedekindRing t transcendental_ratFuncClosureParameter M
      finiteType := finiteTypeRing t transcendental_ratFuncClosureParameter M
      not_isField := notFieldRing t transcendental_ratFuncClosureParameter M
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
  letI : FiniteDimensional K₀ L :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hLM).toLinearMap
      (IntermediateField.inclusion hLM).injective
  letI : Algebra.IsSeparable K₀ L :=
    Algebra.IsSeparable.of_algHom (F := K₀) (E := L) (E' := M)
      (IntermediateField.inclusion hLM)
  letI := dedekindRing t transcendental_ratFuncClosureParameter L
  have hq : (w.comap f).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f.toRingHom
      (RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ eZ.surjective)
        (ringMap_isIntegral hLM)) w
  change (letI := f.toRingHom.toAlgebra; w.ramificationIdx Z.A) * 1 = Z.mult (w.comap f)
  have hidx : (letI := f.toRingHom.toAlgebra; w.ramificationIdx Z.A) =
      (letI := ringMapAlgebra hLM;
        (w : Ideal (coordRing t M)).ramificationIdx (coordRing t L)) :=
    ramificationIdx_equiv_comp eZ.toRingEquiv (ringMap hLM).toRingHom (ringMap_injective hLM)
      (w : Ideal (coordRing t M))
  calc
    _ = 1 * 1 := congrArg (· * 1) (hidx.trans (he w hw))
    _ = 1 := Nat.mul_one 1
    _ = _ := (hZ _ hq).symm

/-- An affine orbicurve cover of multiplicity one has an unramified Galois closure over its source.
The closure ring is fixed precisely over the coordinate ring of the original target. -/
theorem exists_unramified_galoisClosure [CharZero k] {Z Y : AffineOrbicurvePresentation k}
    (ψ : Cover Z Y) (hZ : ∀ w : Ideal Z.A, w.IsMaximal → Z.mult w = 1) :
    ∃ (T : AffineOrbicurvePresentation k) (γ : Cover T Z) (G : Type u) (hG : Group G),
      letI := hG
      ∃ hact : MulSemiringAction G T.A,
        letI := hact
        letI := (γ.f.comp ψ.f).toRingHom.toAlgebra
        IsGaloisGroup G Y.A T.A := by
  letI : CharZero K₀ := charZero_of_injective_algebraMap (algebraMap k K₀).injective
  obtain ⟨F, L, hF, hL, hFL, eY, eZ, hψ⟩ := exists_realization ψ
  let N := IntermediateField.normalClosure K₀ L Ω
  letI : FiniteDimensional K₀ F := hF
  letI : FiniteDimensional K₀ L := hL
  letI : FiniteDimensional K₀ N := inferInstance
  letI : IsGalois K₀ N := by
    letI : Algebra.IsSeparable K₀ N :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact IsGalois.mk
  let M := galoisClosure (N := N) F L
  have hLN : L ≤ N := IntermediateField.le_normalClosure L
  have hLM : L ≤ M := le_galoisClosure hLN
  have hFM : F ≤ M := hFL.trans hLM
  have hMN : M ≤ N := galoisClosure_le
  letI : FiniteDimensional K₀ M :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hMN).toLinearMap
      (IntermediateField.inclusion hMN).injective
  letI : Algebra.IsSeparable K₀ M :=
    Algebra.IsSeparable.of_algHom (F := K₀) (E := M) (E' := N)
      (IntermediateField.inclusion hMN)
  letI : Algebra.IsSeparable K₀ F :=
    Algebra.IsSeparable.of_algHom (F := K₀) (E := F) (E' := N)
      (IntermediateField.inclusion (hFL.trans hLN))
  letI := dedekindRing t transcendental_ratFuncClosureParameter F
  let m : Ideal (coordRing t F) → ℕ := fun q => Y.mult (q.comap eY)
  have hm (w : Ideal (coordRing t L)) (hw : w.IsMaximal) :
      (letI := ringMapAlgebra hFL; w.ramificationIdx (coordRing t F)) =
        m (w.comap (ringMap hFL)) :=
    cover_ramification_of_realization ψ hZ hFL eY eZ hψ w hw
  let γ := unramifiedNormalizationCover hZ eZ hLM
    (galoisClosure_ramificationIdx_eq_one transcendental_ratFuncClosureParameter hFL hLN m hm)
  let G := galoisClosureAutomorphisms (N := N) (F := F) (L := L)
  refine ⟨_, γ, G, inferInstance, inferInstance, ?_⟩
  letI : Algebra Y.A (coordRing t M) := (γ.f.comp ψ.f).toRingHom.toAlgebra
  letI : Algebra (coordRing t F) (coordRing t M) := ringMapAlgebra hFM
  letI : IsGaloisGroup G (coordRing t F) (coordRing t M) := galoisClosure_isGaloisGroup hFM
  refine IsGaloisGroup.of_ringEquiv (G := G) (A := coordRing t F) (A' := Y.A)
    (B := coordRing t M) eY.symm.toRingEquiv ?_
  intro a
  change ringMap hLM (eZ (ψ.f (eY.symm a))) = ringMap hFM a
  rw [hψ, AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The characteristic-zero closure specialized to the complex case of Theorem G. -/
theorem canLift27UnramifiedGaloisClosure : CanLift27UnramifiedGaloisClosure :=
  fun ψ hZ => exists_unramified_galoisClosure ψ hZ

/-- Once automorphism invariance is known, the algebraic closure argument descends the
horizontal coordinate to every common cover target. -/
theorem canLift27ComplexXDescends_of_analytic (hfix : CanLift27ComplexAutomorphismsFixX) :
    CanLift27ComplexXDescends :=
  canLift27ComplexXDescends_of_automorphisms hfix canLift27UnramifiedGaloisClosure

end AbcAdaptation.Reference.Iut.Anabelian
