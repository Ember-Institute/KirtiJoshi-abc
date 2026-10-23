/-
original-path: `refer/iut/Iut/Anabelian/Genuine/Punctured.lean`
original-author: Christian Merten <lana@merten.dev> (Git author)
original-file-authors: The iut contributors
original-coauthor: Claude Opus 5.5 (1M context) <noreply@anthropic.com> (Git trailer)
original-commit: `b51b94cad5c729f753ed0790b5fb95d9d65aaff1`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
license-review: reviewed the source notice and Apache-2.0 LICENSE before copying.
No NOTICE file occurs in the reference tree. Retain the original notice below.
modifications: identify the original polynomial integral closure with the local
actual level-one unsigned normalization. Preserve the coefficient algebra and
ambient embedding. Do not assert an identity with the Weierstrass coordinate ring.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IntegralClosureTransport
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.Normalization

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Genuine/Punctured.lean, puncturedRingEquiv.
fidelity: the actual level-one unsigned normalization is the polynomial
integral closure in the original elliptic function field, by an explicit
coefficient-preserving equivalence with the original ambient embedding.
boundary: Scene1/Derived. This is a normalization identity. An identification
with E.toAffine.CoordinateRing, arbitrary AG.Orbicurve and the producer remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve Polynomial JoshiTeich.Act1Scene1
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

def normalizationPolynomialEquiv : k[X] ≃ₐ[k] Algebra.adjoin k {xG E} :=
  Polynomial.algEquivOfTranscendental k (xG E) (transcendental_xG E)

theorem coe_normalizationPolynomialEquiv (p : k[X]) :
    ((normalizationPolynomialEquiv E p : Algebra.adjoin k {xG E}) : Ω E) =
      aeval (xG E) p := by
  change ((aeval (⟨xG E, Algebra.self_mem_adjoin_singleton k _⟩ : Algebra.adjoin k {xG E}) p :
    Algebra.adjoin k {xG E}) : Ω E) = _
  rw [← Subalgebra.aeval_coe]

def normalizationBaseFunctionFieldEquiv :
    E.toAffine.FunctionField ≃+* normalizationField E 1 ⊥ false :=
  baseFunctionFieldEquiv E

@[simp] theorem coe_normalizationBaseFunctionFieldEquiv (f : E.toAffine.FunctionField) :
    ((normalizationBaseFunctionFieldEquiv E f : normalizationField E 1 ⊥ false) : Ω E) =
      ιF E f := rfl

theorem normalizationBaseFunctionFieldEquiv_algebraMap (p : k[X]) :
    normalizationBaseFunctionFieldEquiv E (algebraMap k[X] E.toAffine.FunctionField p) =
      algebraMap (Algebra.adjoin k {xG E}) (normalizationField E 1 ⊥ false)
        (normalizationPolynomialEquiv E p) := by
  apply Subtype.ext
  rw [coe_normalizationBaseFunctionFieldEquiv, ιF_algebraMap_poly]
  exact (coe_normalizationPolynomialEquiv E p).symm

/-- Compare normalizations using the original curve's function field and polynomial coordinate. -/
def polynomialNormalizationRingEquiv :
    integralClosure k[X] E.toAffine.FunctionField ≃+* coverCoordinateRing E 1 ⊥ false :=
  IntegralClosureTransport.equiv (normalizationPolynomialEquiv E).toRingEquiv
    (normalizationBaseFunctionFieldEquiv E) (normalizationBaseFunctionFieldEquiv_algebraMap E)

@[simp] theorem coe_polynomialNormalizationRingEquiv
    (a : integralClosure k[X] E.toAffine.FunctionField) :
    (((polynomialNormalizationRingEquiv E a : coverCoordinateRing E 1 ⊥ false) :
      normalizationField E 1 ⊥ false) : Ω E) = ιF E (a : E.toAffine.FunctionField) := rfl

def polynomialNormalizationRingAlgEquiv :
    integralClosure k[X] E.toAffine.FunctionField ≃ₐ[k] coverCoordinateRing E 1 ⊥ false :=
  AlgEquiv.ofRingEquiv (f := polynomialNormalizationRingEquiv E) fun c => by
    apply Subtype.ext
    apply Subtype.ext
    exact (ιF E).commutes c

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
