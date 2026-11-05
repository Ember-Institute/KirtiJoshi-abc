import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineDivisionPointTranscendence
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Jacobson.Ring

/-!
source-id: JT-SCENE1-GENUINE-DIVISION-POINT-EVALUATION
source: IUT I Definition 3.1(d); the actual chosen division point and
Weierstrass coordinate-ring evaluation.
fidelity: evaluates the original coordinate ring at the coordinates of the
same actual `Qpt`, and proves injectivity from its transcendental x-coordinate.
boundary: Scene1/Derived. This does not yet extend the evaluation to the
function field or identify its field range.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

private lemma divisionPoint_nonsingular (n : ℕ) :
    (E⁄(Ω E)).toAffine.Nonsingular (ptX (Qpt E n)) (ptY (Qpt E n)) := by
  have hQ : Qpt E n ≠ 0 := by
    change divSys E (effLevel n) ≠ 0
    exact divSys_ne_zero E (effLevel n) (effLevel_pos n)
  cases h : Qpt E n with
  | zero => exact False.elim (hQ h)
  | some x y hxy => exact hxy

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

private theorem isAlgebraic_of_ker_maximal {F A L : Type*} [Field F] [CommRing A]
    [Field L] [Algebra F A] [Algebra F L] [Algebra.FiniteType F A]
    (g : A →ₐ[F] L) (hmax : (RingHom.ker g).IsMaximal) (b : A) :
    IsAlgebraic F (g b) := by
  letI : (RingHom.ker g).IsMaximal := hmax
  letI : Field (A ⧸ RingHom.ker g) := Ideal.Quotient.field _
  letI : Algebra.FiniteType F (A ⧸ RingHom.ker g) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F _) (Ideal.Quotient.mkₐ_surjective F _)
  letI := finite_of_finite_type_of_isJacobsonRing F (A ⧸ RingHom.ker g)
  let ψ : (A ⧸ RingHom.ker g) →ₐ[F] L :=
    Ideal.Quotient.liftₐ (RingHom.ker g) g (fun _ hx => hx)
  have hint : IsIntegral F (Ideal.Quotient.mk (RingHom.ker g) b) := IsIntegral.of_finite F _
  have hint2 : IsIntegral F (ψ (Ideal.Quotient.mk (RingHom.ker g) b)) := hint.map ψ
  have heq : ψ (Ideal.Quotient.mk (RingHom.ker g) b) = g b := by
    simp only [ψ, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    rfl
  rw [heq] at hint2
  exact hint2.isAlgebraic

private def divisionPointCoordinateMap (n : ℕ) :
    E.toAffine.CoordinateRing →+* Ω E := by
  let Q := Qpt E n
  let x := ptX Q
  let y := ptY Q
  let f : k →+* Ω E := algebraMap k (Ω E)
  have h : ((E.toAffine.map f).polynomial).evalEval x y = 0 := by
    change (E.toAffine.baseChange (Ω E)).polynomial.evalEval x y = 0
    exact divisionPoint_nonsingular E n |>.left
  exact AdjoinRoot.lift (eval₂RingHom (algebraMap k (Ω E)) x) y (by
    rw [eval₂_eval₂RingHom_apply]
    rw [← Affine.map_polynomial]
    exact h)

private theorem divisionPointCoordinateMap_X (n : ℕ) :
    divisionPointCoordinateMap E n
        (Affine.CoordinateRing.mk E.toAffine (C Polynomial.X)) = ptX (Qpt E n) := by
  rw [divisionPointCoordinateMap,
    show Affine.CoordinateRing.mk E.toAffine (C Polynomial.X) =
      AdjoinRoot.of E.toAffine.polynomial Polynomial.X from rfl,
    AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_X]

private theorem divisionPointCoordinateMap_algebraMap (n : ℕ) (c : k) :
    divisionPointCoordinateMap E n (algebraMap k E.toAffine.CoordinateRing c) =
      algebraMap k (Ω E) c := by
  have h1 : algebraMap k E.toAffine.CoordinateRing c =
      Affine.CoordinateRing.mk E.toAffine (C (C c)) := by
    rw [IsScalarTower.algebraMap_apply k k[X] E.toAffine.CoordinateRing,
      AdjoinRoot.algebraMap_eq, ← Polynomial.C_eq_algebraMap]
    rfl
  rw [h1, divisionPointCoordinateMap,
    show Affine.CoordinateRing.mk E.toAffine (C (C c)) =
      AdjoinRoot.of E.toAffine.polynomial (C c) from rfl,
    AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_C]

/-- Evaluation of the original affine coordinate ring at the selected actual division point. -/
def divisionPointCoordinateAlgHom (n : ℕ) :
    E.toAffine.CoordinateRing →ₐ[k] Ω E where
  toRingHom := divisionPointCoordinateMap E n
  commutes' := divisionPointCoordinateMap_algebraMap E n

@[simp] theorem divisionPointCoordinateAlgHom_X (n : ℕ) :
    divisionPointCoordinateAlgHom E n
        (Affine.CoordinateRing.mk E.toAffine (C Polynomial.X)) = ptX (Qpt E n) :=
  divisionPointCoordinateMap_X E n

/-- Evaluation at the selected actual division point is injective. -/
theorem divisionPointCoordinateMap_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (divisionPointCoordinateAlgHom E n) := by
  by_contra hni
  have hne : RingHom.ker (divisionPointCoordinateAlgHom E n) ≠ ⊥ := fun hk =>
    hni ((RingHom.injective_iff_ker_eq_bot _).mpr hk)
  haveI hprime : (RingHom.ker (divisionPointCoordinateAlgHom E n)).IsPrime :=
    RingHom.ker_isPrime _
  letI : Ring.DimensionLEOne E.toAffine.CoordinateRing := coordinateRing_dimensionLEOne E
  have hmax : (RingHom.ker (divisionPointCoordinateAlgHom E n)).IsMaximal :=
    hprime.isMaximal hne
  have hx : IsAlgebraic k
      (divisionPointCoordinateAlgHom E n
        (Affine.CoordinateRing.mk E.toAffine (C Polynomial.X))) :=
    isAlgebraic_of_ker_maximal (divisionPointCoordinateAlgHom E n) hmax _
  rw [divisionPointCoordinateAlgHom_X] at hx
  exact (Qpt_xCoord_transcendental E n hn) hx

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
