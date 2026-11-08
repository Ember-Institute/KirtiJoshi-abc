import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.VariableChangePoint
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.FractionRing

/-!
source-id: JT-SCENE1-GENUINE-DIVISION-POINT-EVALUATION
source: IUT I Definition 3.1(d); the actual elliptic function-field translation
route; the project's `GenuineDivisionPointEvaluation.lean` and
`GenuineDivisionPointFunctionFieldEvaluation.lean`; Mathlib's coordinate-ring
quotient and fraction-ring universal properties.
fidelity: evaluates the original Weierstrass coordinate ring at an arbitrary
nonzero point with transcendental x-coordinate, proves injectivity, and extends
the same evaluation to the original function field. The x- and y-coordinate
formulas preserve the supplied point. The proof generalizes the project's
existing division-point evaluation, without a new geometry or existence law.
boundary: Scene1/Derived. This is a reusable evaluation construction, not an
ambient automorphism or a torsion-cusp comparison. Its translation consumer
must supply the actual translated generic point and prove its transcendence.
-/

namespace JoshiTeich.Act1Scene1.WeierstrassTranscendentalPointEvaluation

open WeierstrassCurve Polynomial
open JoshiTeich.ReferenceIut.Anabelian
open scoped Classical

universe u v
noncomputable section

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic]
variable {K : Type v} [Field K] [Algebra k K]

/-- A nonzero affine point has its original nonsingular coordinate presentation. -/
theorem point_nonsingular (P : (E⁄K).toAffine.Point) (hP : P ≠ 0) :
    (E⁄K).toAffine.Nonsingular (ptX P) (ptY P) := by
  cases P with
  | zero => exact False.elim (hP rfl)
  | some x y h => exact h

private theorem coordinateRing_dimensionLEOne :
    Ring.DimensionLEOne E.toAffine.CoordinateRing := by
  letI : Module.Finite k[X] E.toAffine.CoordinateRing :=
    Module.Finite.of_basis (Affine.CoordinateRing.basis E.toAffine)
  letI : Algebra.IsIntegral k[X] E.toAffine.CoordinateRing := inferInstance
  letI : Ring.DimensionLEOne k[X] := Ring.DimensionLEOne.principal_ideal_ring k[X]
  exact Ring.DimensionLEOne.of_isIntegral k[X] E.toAffine.CoordinateRing

private instance coordinateRing_finiteType :
    Algebra.FiniteType k E.toAffine.CoordinateRing := by
  letI : Module.Finite k[X] E.toAffine.CoordinateRing :=
    Module.Finite.of_basis (Affine.CoordinateRing.basis E.toAffine)
  exact Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance

private theorem isAlgebraic_of_ker_maximal
    (g : E.toAffine.CoordinateRing →ₐ[k] K)
    (hmax : (RingHom.ker g).IsMaximal) (b : E.toAffine.CoordinateRing) :
    IsAlgebraic k (g b) := by
  letI : (RingHom.ker g).IsMaximal := hmax
  letI : Field (E.toAffine.CoordinateRing ⧸ RingHom.ker g) := Ideal.Quotient.field _
  letI : Algebra.FiniteType k (E.toAffine.CoordinateRing ⧸ RingHom.ker g) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)
  letI := finite_of_finite_type_of_isJacobsonRing k (E.toAffine.CoordinateRing ⧸ RingHom.ker g)
  let ψ : (E.toAffine.CoordinateRing ⧸ RingHom.ker g) →ₐ[k] K :=
    Ideal.Quotient.liftₐ (RingHom.ker g) g (fun _ hx => hx)
  have hint : IsIntegral k (Ideal.Quotient.mk (RingHom.ker g) b) := IsIntegral.of_finite k _
  have hint2 : IsIntegral k (ψ (Ideal.Quotient.mk (RingHom.ker g) b)) := hint.map ψ
  have heq : ψ (Ideal.Quotient.mk (RingHom.ker g) b) = g b := by
    simp only [ψ, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    rfl
  rw [heq] at hint2
  exact hint2.isAlgebraic

private def coordinateMap (P : (E⁄K).toAffine.Point) (hP : P ≠ 0) :
    E.toAffine.CoordinateRing →+* K := by
  have h : ((E.toAffine.map (algebraMap k K)).polynomial).evalEval (ptX P) (ptY P) = 0 :=
    (point_nonsingular E P hP).left
  exact AdjoinRoot.lift (eval₂RingHom (algebraMap k K) (ptX P)) (ptY P) (by
    rw [eval₂_eval₂RingHom_apply, ← Affine.map_polynomial]
    exact h)

private theorem coordinateMap_algebraMap
    (P : (E⁄K).toAffine.Point) (hP : P ≠ 0) (c : k) :
    coordinateMap E P hP (algebraMap k E.toAffine.CoordinateRing c) = algebraMap k K c := by
  have h1 : algebraMap k E.toAffine.CoordinateRing c =
      Affine.CoordinateRing.mk E.toAffine (C (C c)) := by
    rw [IsScalarTower.algebraMap_apply k k[X] E.toAffine.CoordinateRing,
      AdjoinRoot.algebraMap_eq, ← Polynomial.C_eq_algebraMap]
    rfl
  rw [h1, coordinateMap,
    show Affine.CoordinateRing.mk E.toAffine (C (C c)) =
      AdjoinRoot.of E.toAffine.polynomial (C c) from rfl,
    AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_C]

/-- The original coordinate ring evaluated at the supplied nonzero point. -/
def coordinateAlgHom (P : (E⁄K).toAffine.Point) (hP : P ≠ 0) :
    E.toAffine.CoordinateRing →ₐ[k] K where
  toRingHom := coordinateMap E P hP
  commutes' := coordinateMap_algebraMap E P hP

@[simp] theorem coordinateAlgHom_X (P : (E⁄K).toAffine.Point) (hP : P ≠ 0) :
    coordinateAlgHom E P hP (Affine.CoordinateRing.mk E.toAffine (C Polynomial.X)) = ptX P := by
  change coordinateMap E P hP _ = _
  rw [coordinateMap,
    show Affine.CoordinateRing.mk E.toAffine (C Polynomial.X) =
      AdjoinRoot.of E.toAffine.polynomial Polynomial.X from rfl,
    AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_X]

@[simp] theorem coordinateAlgHom_Y (P : (E⁄K).toAffine.Point) (hP : P ≠ 0) :
    coordinateAlgHom E P hP (Affine.CoordinateRing.mk E.toAffine Polynomial.X) = ptY P := by
  change coordinateMap E P hP (AdjoinRoot.root E.toAffine.polynomial) = _
  rw [coordinateMap, AdjoinRoot.lift_root]

/-- Coordinate maps are determined by the two original Weierstrass coordinates. -/
theorem coordinateAlgHom_ext
    {f g : E.toAffine.CoordinateRing →ₐ[k] K}
    (hx : f (Affine.CoordinateRing.mk E.toAffine (C Polynomial.X)) =
      g (Affine.CoordinateRing.mk E.toAffine (C Polynomial.X)))
    (hy : f (Affine.CoordinateRing.mk E.toAffine Polynomial.X) =
      g (Affine.CoordinateRing.mk E.toAffine Polynomial.X)) : f = g := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    exact hx
  · exact hy

/-- Transcendence of the supplied x-coordinate forces coordinate evaluation to be injective. -/
theorem coordinateAlgHom_injective
    (P : (E⁄K).toAffine.Point) (hP : P ≠ 0) (hx : Transcendental k (ptX P)) :
    Function.Injective (coordinateAlgHom E P hP) := by
  by_contra hni
  have hne : RingHom.ker (coordinateAlgHom E P hP) ≠ ⊥ := fun hk =>
    hni ((RingHom.injective_iff_ker_eq_bot _).mpr hk)
  haveI hprime : (RingHom.ker (coordinateAlgHom E P hP)).IsPrime := RingHom.ker_isPrime _
  letI : Ring.DimensionLEOne E.toAffine.CoordinateRing := coordinateRing_dimensionLEOne E
  have hmax : (RingHom.ker (coordinateAlgHom E P hP)).IsMaximal := hprime.isMaximal hne
  have hAlg := isAlgebraic_of_ker_maximal E (coordinateAlgHom E P hP) hmax
    (Affine.CoordinateRing.mk E.toAffine (C Polynomial.X))
  rw [coordinateAlgHom_X] at hAlg
  exact hx hAlg

/-- Extend the same injective evaluation to the original elliptic function field. -/
def functionFieldAlgHom
    (P : (E⁄K).toAffine.Point) (hP : P ≠ 0) (hx : Transcendental k (ptX P)) :
    E.toAffine.FunctionField →ₐ[k] K :=
  IsFractionRing.liftAlgHom (coordinateAlgHom_injective E P hP hx)

@[simp] theorem functionFieldAlgHom_algebraMap
    (P : (E⁄K).toAffine.Point) (hP : P ≠ 0) (hx : Transcendental k (ptX P))
    (a : E.toAffine.CoordinateRing) :
    functionFieldAlgHom E P hP hx (algebraMap _ E.toAffine.FunctionField a) =
      coordinateAlgHom E P hP a :=
  IsFractionRing.lift_algebraMap (coordinateAlgHom_injective E P hP hx) a

@[simp] theorem functionFieldAlgHom_X
    (P : (E⁄K).toAffine.Point) (hP : P ≠ 0) (hx : Transcendental k (ptX P)) :
    functionFieldAlgHom E P hP hx
      (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField
        (Affine.CoordinateRing.mk E.toAffine (C Polynomial.X))) = ptX P := by
  rw [functionFieldAlgHom_algebraMap, coordinateAlgHom_X]

@[simp] theorem functionFieldAlgHom_Y
    (P : (E⁄K).toAffine.Point) (hP : P ≠ 0) (hx : Transcendental k (ptX P)) :
    functionFieldAlgHom E P hP hx
      (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField
        (Affine.CoordinateRing.mk E.toAffine Polynomial.X)) = ptY P := by
  rw [functionFieldAlgHom_algebraMap, coordinateAlgHom_Y]

/-- The function-field maps are determined by the same original two coordinates. -/
theorem functionFieldAlgHom_ext
    {f g : E.toAffine.FunctionField →ₐ[k] K}
    (hx : f (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField
        (Affine.CoordinateRing.mk E.toAffine (C Polynomial.X))) =
      g (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField
        (Affine.CoordinateRing.mk E.toAffine (C Polynomial.X))))
    (hy : f (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField
        (Affine.CoordinateRing.mk E.toAffine Polynomial.X)) =
      g (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField
        (Affine.CoordinateRing.mk E.toAffine Polynomial.X))) : f = g := by
  let ι := IsScalarTower.toAlgHom k E.toAffine.CoordinateRing E.toAffine.FunctionField
  have hc : f.comp ι = g.comp ι := coordinateAlgHom_ext E hx hy
  apply AlgHom.toRingHom_injective
  apply IsFractionRing.ringHom_ext (A := E.toAffine.CoordinateRing)
  intro a
  exact AlgHom.congr_fun hc a

end
end JoshiTeich.Act1Scene1.WeierstrassTranscendentalPointEvaluation
