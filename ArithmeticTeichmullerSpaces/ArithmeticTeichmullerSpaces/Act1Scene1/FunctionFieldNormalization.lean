/-
original-path: `refer/iut/.lake/packages/pi1/Pi1/Orbicurve/Subfield.lean`
original-author: Christian Merten <lana@merten.dev> (Git author; no author header in source)
original-commit: `0d1866c753ee060d887455ab42a3e0fead548cfb`
source-snapshot: `ca7def953193f861a462aa0831eec8f0a31ff69f` (pi1 package)
license: Apache-2.0 (see project `LICENSE`)
license-review: the source has no per-file copyright notice; reviewed the package's
Apache-2.0 LICENSE before copying. The project retains that license text.
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Realize.lean`, integral-closure realization.
fidelity: extracted normalization-ring algebra and injective/integral inclusion
proofs, without the AffOrbicurve or etale interface. Added fraction-field identity
and a carrier-preserving rebase along a proved equality of coefficient fields.
boundary: Scene1/Derived; no orbicurve, core, or theta-root law is assumed.
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Adjoin.Polynomial.Transcendental

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open Polynomial IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin Classical
universe u
noncomputable section

set_option maxHeartbeats 1000000

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]

/-- Change the named base field along an equality, preserving the actual ambient subfield. -/
def rebaseField {B B' : IntermediateField k Ω} (h : B = B')
    (L : IntermediateField B Ω) : IntermediateField B' Ω :=
  L.toSubfield.toIntermediateField (fun x => by
    have hx : (x : Ω) ∈ B := h.symm ▸ x.2
    exact L.algebraMap_mem ⟨x, hx⟩)

lemma mem_rebaseField {B B' : IntermediateField k Ω} (h : B = B')
    (L : IntermediateField B Ω) (x : Ω) : x ∈ rebaseField h L ↔ x ∈ L := Iff.rfl

lemma finiteDimensional_rebaseField {B B' : IntermediateField k Ω} (h : B = B')
    (L : IntermediateField B Ω) [FiniteDimensional B L] :
    FiniteDimensional B' (rebaseField h L) := by
  subst B'
  change FiniteDimensional B L
  infer_instance

lemma rebaseField_mono {B B' : IntermediateField k Ω} (h : B = B')
    {L L' : IntermediateField B Ω} (hL : L ≤ L') : rebaseField h L ≤ rebaseField h L' := hL

abbrev polynomialBase (k : Type u) [Field k] [Algebra k Ω] (t : Ω) := Algebra.adjoin k {t}
abbrev rationalBase (k : Type u) [Field k] [Algebra k Ω] (t : Ω) := IntermediateField.adjoin k {t}

variable (t : Ω)

abbrev coordRing (L : IntermediateField (rationalBase k t) Ω) :=
  integralClosure (polynomialBase k t) L

instance towerBase (L : IntermediateField (rationalBase k t) Ω) :
    IsScalarTower k (polynomialBase k t) L := IsScalarTower.of_algebraMap_eq fun _ => rfl

instance faithfulBase (L : IntermediateField (rationalBase k t) Ω) :
    FaithfulSMul (polynomialBase k t) L := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro a b h
  exact Subtype.ext (congrArg (fun x : L => (x : Ω)) h)

variable (ht : Transcendental k t)
include ht

lemma principalBase : IsPrincipalIdealRing (polynomialBase k t) :=
  IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental k t ht).toRingHom
    (Polynomial.algEquivOfTranscendental k t ht).surjective

lemma dedekindBase : IsDedekindDomain (polynomialBase k t) :=
  have := principalBase t ht
  inferInstance

lemma finiteTypeBase : Algebra.FiniteType k (polynomialBase k t) :=
  Algebra.FiniteType.equiv inferInstance (Polynomial.algEquivOfTranscendental k t ht)

lemma notFieldBase : ¬ IsField (polynomialBase k t) := by
  intro h
  exact Polynomial.not_isField k
    (MulEquiv.isField h (Polynomial.algEquivOfTranscendental k t ht).toMulEquiv)

variable (L : IntermediateField (rationalBase k t) Ω)
  [FiniteDimensional (rationalBase k t) L] [Algebra.IsSeparable (rationalBase k t) L]

lemma dedekindRing : IsDedekindDomain (coordRing t L) :=
  have := dedekindBase t ht
  integralClosure.isDedekindDomain (polynomialBase k t) (rationalBase k t) L

lemma finiteRing : Module.Finite (polynomialBase k t) (coordRing t L) :=
  have := dedekindBase t ht
  IsIntegralClosure.finite (polynomialBase k t) (rationalBase k t) L (coordRing t L)

omit ht in
lemma fractionFieldRing : IsFractionRing (coordRing t L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (polynomialBase k t) (rationalBase k t) L (coordRing t L)

lemma finiteTypeRing : Algebra.FiniteType k (coordRing t L) := by
  have := finiteRing t ht L
  have := finiteTypeBase t ht
  exact Algebra.FiniteType.trans (S := polynomialBase k t) inferInstance inferInstance

lemma notFieldRing : ¬ IsField (coordRing t L) := by
  intro hC
  refine notFieldBase t ht (isField_of_isIntegral_of_isField ?_ hC)
  intro a b hab
  have h := congrArg (fun c : coordRing t L => ((c : L) : Ω)) hab
  exact Subtype.val_injective (by simpa using h)

omit ht
variable {t L}

/-- The integral-closure map induced by a literal inclusion of ambient fields. -/
def ringMap {L L' : IntermediateField (rationalBase k t) Ω} (h : L ≤ L') :
    coordRing t L →ₐ[k] coordRing t L' where
  toFun a := ⟨IntermediateField.inclusion h a, by
    have ha := a.2
    rw [mem_integralClosure_iff] at ha ⊢
    exact ha.map ((IntermediateField.inclusion h).restrictScalars (polynomialBase k t))⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] lemma coe_ringMap {L L' : IntermediateField (rationalBase k t) Ω}
    (h : L ≤ L') (a : coordRing t L) :
    ((ringMap h a : L') : Ω) = ((a : L) : Ω) := rfl

lemma ringMap_injective {L L' : IntermediateField (rationalBase k t) Ω} (h : L ≤ L') :
    Function.Injective (ringMap h) := by
  intro a b hab
  have h := congrArg (fun c : coordRing t L' => ((c : L') : Ω)) hab
  simp only [coe_ringMap] at h
  exact Subtype.val_injective (Subtype.val_injective h)

lemma ringMap_isIntegral {L L' : IntermediateField (rationalBase k t) Ω} (h : L ≤ L') :
    (ringMap h).toRingHom.IsIntegral := by
  intro b
  obtain ⟨p, hp, hpb⟩ := integralClosure.isIntegral (R := polynomialBase k t) (A := L') b
  refine ⟨p.map (algebraMap (polynomialBase k t) (coordRing t L)), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hc : (ringMap h).toRingHom.comp
      (algebraMap (polynomialBase k t) (coordRing t L)) =
        algebraMap (polynomialBase k t) (coordRing t L') := RingHom.ext fun _ => rfl
  rw [hc]
  exact hpb

end
end JoshiTeich.Act1Scene1.FunctionFieldNormalization
