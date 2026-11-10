import ArithmeticTeichmullerSpaces.Act1Scene1.ValuationResidueCoefficients
import ArithmeticTeichmullerSpaces.Act1Scene1.IntegralDivisionCoordinates

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
additional-source-ids: IUT-COR312-GEOMETRIC-TORSION-COUNT
source: IUT I Definition 3.1(b),(d),(f); Joshi III `ss:theta-data-fixing2`;
the exact completed-square multiplication-fibre equation and the strict
target-minus-constant valuation bound at the same valuation subring.
fidelity: specializes the original integral x-coordinate, without choosing
another root or assuming that its residue belongs to the coefficient field.
The specialization map has domain W, not the ambient fraction field K.
Original composition of existing project and Mathlib theorems; no reference
proof code copied.
boundary: the root is in the actual valuation residue field. This theorem
does not assert rationality of that root or identify the upper residue field.
-/

namespace JoshiTeich.Act1Scene1.ValuationFiberSpecialization

open WeierstrassCurve Polynomial
open JoshiTeich.ReferenceIut
open IntegralDivisionCoordinates ValuationResidueCoefficients

noncomputable section

section RingMaps

variable {k A K F : Type*} [CommRing k] [CommRing A] [CommRing K] [CommRing F]

/-- An exact polynomial evaluation descends through the integral coefficient
ring, then maps to its residue ring. -/
theorem map_eval_sub_mul_zero
    (i : k →+* A) (j : A →+* K) (ρ : A →+* F)
    (hj : Function.Injective j) (p q : k[X]) (x target : A)
    (heq : (p.map (j.comp i)).eval (j x) -
      j target * (q.map (j.comp i)).eval (j x) = 0) :
    (p.map (ρ.comp i)).eval (ρ x) -
      ρ target * (q.map (ρ.comp i)).eval (ρ x) = 0 := by
  have hpj : j ((p.map i).eval x) = (p.map (j.comp i)).eval (j x) := by
    rw [← Polynomial.eval_map_apply, Polynomial.map_map]
  have hqj : j ((q.map i).eval x) = (q.map (j.comp i)).eval (j x) := by
    rw [← Polynomial.eval_map_apply, Polynomial.map_map]
  have hA : (p.map i).eval x - target * (q.map i).eval x = 0 := by
    apply hj
    rw [map_sub, map_mul, map_zero, hpj, hqj]
    exact heq
  have hpρ : ρ ((p.map i).eval x) = (p.map (ρ.comp i)).eval (ρ x) := by
    rw [← Polynomial.eval_map_apply, Polynomial.map_map]
  have hqρ : ρ ((q.map i).eval x) = (q.map (ρ.comp i)).eval (ρ x) := by
    rw [← Polynomial.eval_map_apply, Polynomial.map_map]
  have hρ := congrArg ρ hA
  rwa [map_sub, map_mul, map_zero, hpρ, hqρ] at hρ

/-- Descend the original equation through an injective integral-ring map,
then send its two original coordinates to the residue ring. -/
theorem map_equation_of_injective
    (E : WeierstrassCurve k)
    (i : k →+* A) (j : A →+* K) (ρ : A →+* F)
    (hj : Function.Injective j) (x y : A)
    (heq : (E.map (j.comp i)).toAffine.Equation (j x) (j y)) :
    (E.map (ρ.comp i)).toAffine.Equation (ρ x) (ρ y) := by
  have hjEq : ((E.map i).map j).toAffine.Equation (j x) (j y) := by
    simpa only [WeierstrassCurve.map_map] using heq
  have hA : (E.map i).toAffine.Equation x y :=
    (Affine.map_equation (E.map i).toAffine (f := j) hj x y).mp hjEq
  have hF := Affine.Equation.map ρ hA
  simpa only [WeierstrassCurve.map_map] using hF


end RingMaps

universe u v
variable {k : Type u} [Field k] [CharZero k] {K : Type v} [Field K] [Algebra k K]

/-- Specialization of the exact completed-square division-fibre equation at
the same integral coordinate. -/
theorem short_fibre_isRoot
    (E : WeierstrassCurve k) (W : ValuationSubring K)
    (hk : ∀ c : k, algebraMap k K c ∈ W) (n : ℕ) (r : k)
    {x target : K} (hx : x ∈ W) (ht : target ∈ W)
    (heq : (((shortModel E)⁄K).Φ n).eval x -
      target * (((shortModel E)⁄K).ΨSq n).eval x = 0)
    (hclose : W.valuation (target - algebraMap k K r) < 1) :
    letI := coefficientAlgebra W hk
    (Torsion.fibrePoly (((shortModel E)⁄(residueField W)).toAffine) n
      (algebraMap k (residueField W) r)).IsRoot
        (IsLocalRing.residue W ⟨x, hx⟩) := by
  letI := coefficientAlgebra W hk
  have hcomp : W.subtype.comp (coefficientMap W hk) = algebraMap k K := by
    ext c
    rfl
  have hrcomp : (IsLocalRing.residue W).comp (coefficientMap W hk) =
      algebraMap k (residueField W) := by
    ext c
    rfl
  have hΦK : ((shortModel E)⁄K).Φ n =
      ((shortModel E).Φ n).map (algebraMap k K) := map_Φ _ _ _
  have hΨK : ((shortModel E)⁄K).ΨSq n =
      ((shortModel E).ΨSq n).map (algebraMap k K) := map_ΨSq _ _ _
  rw [hΦK, hΨK] at heq
  have hres := map_eval_sub_mul_zero
    (coefficientMap W hk) W.subtype (IsLocalRing.residue W)
    Subtype.val_injective ((shortModel E).Φ n) ((shortModel E).ΨSq n)
    ⟨x, hx⟩ ⟨target, ht⟩
    (by simpa only [hcomp, ValuationSubring.subtype_apply] using heq)
  rw [hrcomp] at hres
  have htres : IsLocalRing.residue W ⟨target, ht⟩ =
      algebraMap k (residueField W) r :=
    (residue_eq_of_sub_lt_one W ⟨target, ht⟩
      ⟨algebraMap k K r, hk r⟩ hclose).trans (residue_algebraMap W hk r)
  change (Torsion.fibrePoly (((shortModel E)⁄(residueField W)).toAffine) n
    (algebraMap k (residueField W) r)).eval _ = 0
  simp only [Torsion.fibrePoly, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C]
  have hΦκ : ((shortModel E)⁄(residueField W)).Φ n =
      ((shortModel E).Φ n).map (algebraMap k (residueField W)) := map_Φ _ _ _
  have hΨκ : ((shortModel E)⁄(residueField W)).ΨSq n =
      ((shortModel E).ΨSq n).map (algebraMap k (residueField W)) := map_ΨSq _ _ _
  rw [hΦκ, hΨκ]
  simpa only [htres] using hres

/-- Both original integral coordinates satisfy the original reduced model. -/
theorem equation_residue
    (E : WeierstrassCurve k) (W : ValuationSubring K)
    (hk : ∀ c : k, algebraMap k K c ∈ W)
    {x y : K} (hx : x ∈ W) (hy : y ∈ W)
    (heq : (E⁄K).toAffine.Equation x y) :
    letI := coefficientAlgebra W hk
    (E⁄(residueField W)).toAffine.Equation
      (IsLocalRing.residue W ⟨x, hx⟩) (IsLocalRing.residue W ⟨y, hy⟩) := by
  letI := coefficientAlgebra W hk
  have hcomp : W.subtype.comp (coefficientMap W hk) = algebraMap k K := by
    ext c
    rfl
  have hrcomp : (IsLocalRing.residue W).comp (coefficientMap W hk) =
      algebraMap k (residueField W) := by
    ext c
    rfl
  have hres := map_equation_of_injective E
    (coefficientMap W hk) W.subtype (IsLocalRing.residue W)
    Subtype.val_injective ⟨x, hx⟩ ⟨y, hy⟩
    (by simpa only [hcomp, ValuationSubring.subtype_apply,
      WeierstrassCurve.baseChange] using heq)
  simpa only [hrcomp, WeierstrassCurve.baseChange] using hres


end
end JoshiTeich.Act1Scene1.ValuationFiberSpecialization
