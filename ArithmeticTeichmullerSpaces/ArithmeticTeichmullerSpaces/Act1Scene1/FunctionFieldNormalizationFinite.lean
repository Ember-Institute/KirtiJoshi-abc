/-
original-path: `refer/iut/.lake/packages/pi1/Pi1/Orbicurve/SubfieldGalois.lean`
original-author: Christian Merten <lana@merten.dev> (Git author; no author header in source)
original-commit: `1314bc8d47c13db19b895144391571f1ac5ecfab`
source-snapshot: `ca7def953193f861a462aa0831eec8f0a31ff69f` (pi1 package)
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the package LICENSE; the source has no per-file copyright
notice and the package has no NOTICE file. The project retains the license text.
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`SubfieldGalois.lean`, `algRing` and `module_finite_ringMap`.
fidelity: ports the scalar-restriction proof of finiteness to the local actual
normalization rings. Adds the RingHom.Finite formulation used by affine spectra.
boundary: Scene1/Derived; no Galois, ramification or etaleness law is assumed.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalization
import Mathlib.RingTheory.RingHom.Finite

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open scoped IntermediateField.algebraAdjoinAdjoin Classical
universe u
noncomputable section

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
variable {t : Ω} {L L' : IntermediateField (rationalBase k t) Ω}

/-- The algebra structure induced by the actual inclusion of normalization rings. -/
abbrev ringMapAlgebra (h : L ≤ L') : Algebra (coordRing t L) (coordRing t L') :=
  (ringMap h).toRingHom.toAlgebra

lemma moduleFinite_ringMap [FiniteDimensional (rationalBase k t) L']
    [Algebra.IsSeparable (rationalBase k t) L'] (ht : Transcendental k t) (h : L ≤ L') :
    @Module.Finite (coordRing t L) (coordRing t L') _ _ (ringMapAlgebra h).toModule := by
  letI iR := ringMapAlgebra h
  letI : SMul (coordRing t L) (coordRing t L') := iR.toSMul
  letI : Module (coordRing t L) (coordRing t L') := iR.toModule
  haveI := finiteRing t ht L'
  haveI : IsScalarTower (polynomialBase k t) (coordRing t L) (coordRing t L') :=
    ⟨fun a b c => by
      apply Subtype.ext
      apply Subtype.ext
      change ((a : Ω) * (b : Ω)) * (c : Ω) = (a : Ω) * ((b : Ω) * (c : Ω))
      exact mul_assoc _ _ _⟩
  exact Module.Finite.of_restrictScalars_finite (polynomialBase k t)
    (coordRing t L) (coordRing t L')

lemma ringMap_finite [FiniteDimensional (rationalBase k t) L']
    [Algebra.IsSeparable (rationalBase k t) L'] (ht : Transcendental k t) (h : L ≤ L') :
    (ringMap h).toRingHom.Finite :=
  moduleFinite_ringMap ht h

end
end JoshiTeich.Act1Scene1.FunctionFieldNormalization
