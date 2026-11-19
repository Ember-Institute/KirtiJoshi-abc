/-
Source: Pi1/Orbicurve/EllipticSubfield.lean and Pi1/Orbicurve/Lefschetz.lean
at revision ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.
-/
import Solutions.Source_ReferenceIutCanLiftPresentation
import Solutions.Source_ReferenceIutCanLiftSignMultiplicity
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedBaseNormalizationRing
import ArithmeticTeichmullerSpaces.Act1Scene1.WeierstrassTranscendentalPointEvaluation

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.Anabelian

open Polynomial WeierstrassCurve JoshiTeich.Act1Scene1
open JoshiTeich.Act1Scene1.FunctionFieldNormalization
open JoshiTeich.Act1Scene1.WeierstrassTranscendentalPointEvaluation
open JoshiTeich.ReferenceIut.Anabelian.Genuine
open scoped IntermediateField.algebraAdjoinAdjoin

universe u

noncomputable section

variable {k K Ω : Type u} [Field k] [Field K] [Field Ω] [Algebra k Ω] [Algebra K Ω]

/-- The coefficient of `Y` when the Weierstrass equation is evaluated at `t`. -/
def weierstrassQuadraticB (E : WeierstrassCurve k) (t : Ω) : Ω :=
  algebraMap k Ω E.a₁ * t + algebraMap k Ω E.a₃

/-- The right-hand side of the Weierstrass equation evaluated at `t`. -/
def weierstrassQuadraticC (E : WeierstrassCurve k) (t : Ω) : Ω :=
  t ^ 3 + algebraMap k Ω E.a₂ * t ^ 2 + algebraMap k Ω E.a₄ * t + algebraMap k Ω E.a₆

theorem weierstrassQuadraticB_mem (E : WeierstrassCurve k) (t : Ω) :
    weierstrassQuadraticB E t ∈ rationalBase k t := by
  let B := rationalBase k t
  have ht : t ∈ B := IntermediateField.mem_adjoin_simple_self k t
  exact add_mem (mul_mem (B.algebraMap_mem E.a₁) ht) (B.algebraMap_mem E.a₃)

theorem weierstrassQuadraticC_mem (E : WeierstrassCurve k) (t : Ω) :
    weierstrassQuadraticC E t ∈ rationalBase k t := by
  let B := rationalBase k t
  have ht : t ∈ B := IntermediateField.mem_adjoin_simple_self k t
  exact add_mem (add_mem (add_mem (pow_mem ht 3)
    (mul_mem (B.algebraMap_mem E.a₂) (pow_mem ht 2))) (mul_mem (B.algebraMap_mem E.a₄) ht))
    (B.algebraMap_mem E.a₆)

section Constants

variable [Algebra k K] [IsScalarTower k K Ω]

theorem weierstrassQuadraticB_map (E : WeierstrassCurve k) (t : Ω) :
    weierstrassQuadraticB (E.map (algebraMap k K)) t = weierstrassQuadraticB E t := by
  simp only [weierstrassQuadraticB, map_a₁, map_a₃, ← IsScalarTower.algebraMap_apply k K Ω]

theorem weierstrassQuadraticC_map (E : WeierstrassCurve k) (t : Ω) :
    weierstrassQuadraticC (E.map (algebraMap k K)) t = weierstrassQuadraticC E t := by
  simp only [weierstrassQuadraticC, map_a₂, map_a₄, map_a₆, ← IsScalarTower.algebraMap_apply k K Ω]

end Constants

section FunctionField

variable (E : WeierstrassCurve k) [hElliptic : E.IsElliptic]

include hElliptic in
/-- A transcendental solution of the Weierstrass equation gives an embedding of its
function field with the indicated coordinates. -/
theorem exists_functionField_embedding_of_quadratic {t y : Ω} (ht : Transcendental k t)
    (hy : y ^ 2 + weierstrassQuadraticB E t * y = weierstrassQuadraticC E t) :
    ∃ j : E.toAffine.FunctionField →ₐ[k] Ω, j (xF E) = t ∧ j (yF E) = y := by
  letI : (E⁄Ω).IsElliptic := inferInstanceAs (E.map (algebraMap k Ω)).IsElliptic
  have hns : (E⁄Ω).toAffine.Nonsingular t y := by
    rw [← Affine.equation_iff_nonsingular, Affine.equation_iff]
    change y ^ 2 + algebraMap k Ω E.a₁ * t * y + algebraMap k Ω E.a₃ * y =
      t ^ 3 + algebraMap k Ω E.a₂ * t ^ 2 + algebraMap k Ω E.a₄ * t + algebraMap k Ω E.a₆
    simpa only [weierstrassQuadraticB, weierstrassQuadraticC, add_mul, ← add_assoc] using hy
  let P : (E⁄Ω).toAffine.Point := Affine.Point.some t y hns
  have hP : P ≠ 0 := by
    change Affine.Point.some t y hns ≠ Affine.Point.zero
    intro h
    cases h
  have htP : Transcendental k (JoshiTeich.ReferenceIut.Anabelian.ptX P) := ht
  exact ⟨functionFieldAlgHom E P hP htP, functionFieldAlgHom_X E P hP htP,
    functionFieldAlgHom_Y E P hP htP⟩

variable [hCharZero : CharZero k] (j : E.toAffine.FunctionField →ₐ[k] Ω)

include hCharZero hElliptic in
theorem transcendental_functionField_x : Transcendental k (j (xF E)) := by
  intro h
  have hx : IsAlgebraic k (xF E) := (isAlgebraic_algHom_iff j j.injective).mp h
  exact transcendental_xG E ((isAlgebraic_algHom_iff (ιF E) (ιF E).injective).mpr hx)

theorem functionField_quadratic :
    j (yF E) ^ 2 + weierstrassQuadraticB E (j (xF E)) * j (yF E) =
      weierstrassQuadraticC E (j (xF E)) := by
  have h : (E⁄Ω).toAffine.Equation (j (xF E)) (j (yF E)) := (equation_xF_yF E).baseChange j
  rw [Affine.equation_iff] at h
  simpa only [weierstrassQuadraticB, weierstrassQuadraticC, baseChange, map_a₁, map_a₂, map_a₃,
    map_a₄, map_a₆, add_mul, ← add_assoc] using h

private theorem functionField_aeval_x (p : k[X]) :
    j (algebraMap k[X] E.toAffine.FunctionField p) = aeval (j (xF E)) p := by
  have hX : algebraMap k[X] E.toAffine.FunctionField X = xF E := by
    rw [IsScalarTower.algebraMap_apply k[X] E.toAffine.CoordinateRing]
    rfl
  have hp : aeval (xF E) p = algebraMap k[X] E.toAffine.FunctionField p := by
    rw [← hX, aeval_algebraMap_apply, aeval_X_left_apply]
  rw [← hp, Polynomial.aeval_algHom_apply]

local notation "t" => j (xF E)
local notation "y" => j (yF E)
local notation "N" => quadraticParameterField k t y

private theorem functionField_mem_quadratic (a : E.toAffine.FunctionField) : j a ∈ N := by
  have hymem : y ∈ N := IntermediateField.mem_adjoin_simple_self (rationalBase k t) y
  have hpoly (p : k[X]) : j (algebraMap k[X] E.toAffine.FunctionField p) ∈ N := by
    rw [functionField_aeval_x]
    exact (N).algebraMap_mem ⟨_, IntermediateField.algebra_adjoin_le_adjoin k {t}
      (Polynomial.aeval_mem_adjoin_singleton k t)⟩
  have hcoord (a : E.toAffine.CoordinateRing) :
      j (algebraMap E.toAffine.CoordinateRing E.toAffine.FunctionField a) ∈ N := by
    obtain ⟨p, q, rfl⟩ := Affine.CoordinateRing.exists_smul_basis_eq a
    simp only [Algebra.smul_def, mul_one, map_add, map_mul,
      ← IsScalarTower.algebraMap_apply k[X] E.toAffine.CoordinateRing E.toAffine.FunctionField]
    exact add_mem (hpoly p) (mul_mem (hpoly q) hymem)
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := E.toAffine.CoordinateRing) a
  rw [map_div₀]
  exact div_mem (hcoord a) (hcoord b)

private theorem functionField_range_eq_quadratic : j.fieldRange = (N).restrictScalars k := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact functionField_mem_quadratic E j a
  · have hbase : rationalBase k t ≤ j.fieldRange :=
      IntermediateField.adjoin_simple_le_iff.mpr ⟨xF E, rfl⟩
    let J : IntermediateField (rationalBase k t) Ω := IntermediateField.extendScalars hbase
    have hN : N ≤ J := IntermediateField.adjoin_simple_le_iff.mpr
      (show y ∈ J from ⟨yF E, rfl⟩)
    exact fun _ ha => hN ha

private def functionFieldEquivQuadratic : E.toAffine.FunctionField ≃ₐ[k] N :=
  j.equivFieldRange.trans (IntermediateField.equivOfEq (functionField_range_eq_quadratic E j))

private theorem functionFieldEquivQuadratic_coe (a : E.toAffine.FunctionField) :
    ((functionFieldEquivQuadratic E j a : N) : Ω) = j a := by
  change (j.equivFieldRange a : Ω) = j a
  exact j.equivFieldRange_apply_coe a

private def originalPolynomialEquiv : k[X] ≃ₐ[k] polynomialBase k t :=
  Polynomial.algEquivOfTranscendental k t (transcendental_functionField_x E j)

private theorem originalPolynomialEquiv_coe (p : k[X]) :
    (originalPolynomialEquiv E j p : Ω) = aeval t p := by
  change ((aeval (⟨t, Algebra.self_mem_adjoin_singleton k t⟩ : polynomialBase k t) p :
    polynomialBase k t) : Ω) = _
  rw [← Subalgebra.aeval_coe]

private theorem functionFieldEquivQuadratic_algebraMap (p : k[X]) :
    functionFieldEquivQuadratic E j (algebraMap k[X] E.toAffine.FunctionField p) =
      algebraMap (polynomialBase k t) N (originalPolynomialEquiv E j p) := by
  apply Subtype.ext
  change ((functionFieldEquivQuadratic E j (algebraMap k[X] E.toAffine.FunctionField p) :
    N) : Ω) = (originalPolynomialEquiv E j p : Ω)
  rw [functionFieldEquivQuadratic_coe, functionField_aeval_x, originalPolynomialEquiv_coe]

private def unsignedQuadraticModelTransport :
    integralClosure k[X] E.toAffine.FunctionField ≃+* coordRing t N :=
  IntegralClosureTransport.equiv (originalPolynomialEquiv E j).toRingEquiv
    (functionFieldEquivQuadratic E j).toRingEquiv (functionFieldEquivQuadratic_algebraMap E j)

private theorem coordRingVal_unsignedQuadraticModelTransport
    (a : integralClosure k[X] E.toAffine.FunctionField) :
    coordRingVal t (B := N) (unsignedQuadraticModelTransport E j a) = j (a : E.toAffine.FunctionField) := by
  change (((unsignedQuadraticModelTransport E j a : coordRing t N) : N) : Ω) = _
  rw [unsignedQuadraticModelTransport, IntegralClosureTransport.coe_equiv] <;>
    exact functionFieldEquivQuadratic_coe E j (a : E.toAffine.FunctionField)

/-- The actual unsigned normalization ring, realized at the same coordinates in `Ω`. -/
def unsignedQuadraticModelEquiv : coverCoordinateRing E 1 ⊥ false ≃ₐ[k] coordRing t N :=
  (polynomialNormalizationRingAlgEquiv E).symm.trans
    (AlgEquiv.ofRingEquiv (f := unsignedQuadraticModelTransport E j) fun c => by
      apply coordRingVal_injective t (B := N)
      exact (coordRingVal_unsignedQuadraticModelTransport E j _).trans (j.commutes c))

/-- The signed normalization ring identifies with the bottom normalization of the same `t`-line. -/
def signedQuadraticModelEquiv : coverCoordinateRing E 1 ⊥ true ≃ₐ[k]
    coordRing t (⊥ : IntermediateField (rationalBase k t) Ω) :=
  (signedBasePolynomialAlgEquiv E).symm.trans
    (constantExtensionLineEquiv (transcendental_functionField_x E j))

private theorem coordRingVal_unsignedQuadraticModelEquiv_integralClosure
    (a : integralClosure k[X] E.toAffine.FunctionField) :
    coordRingVal t (B := N) (unsignedQuadraticModelEquiv E j
      (polynomialNormalizationRingAlgEquiv E a)) = j (a : E.toAffine.FunctionField) := by
  let e := polynomialNormalizationRingAlgEquiv E
  change coordRingVal t (B := N) (unsignedQuadraticModelTransport E j (e.symm (e a))) = _
  exact (congrArg (fun b => coordRingVal t (B := N) (unsignedQuadraticModelTransport E j b))
    (e.symm_apply_apply a)).trans (coordRingVal_unsignedQuadraticModelTransport E j a)

private theorem coordRingVal_unsignedQuadraticModelEquiv_polynomial (p : k[X]) :
    coordRingVal t (B := N) (unsignedQuadraticModelEquiv E j
      (signedNormalizationRingMap E 1 ⊥ (signedBasePolynomialAlgEquiv E p))) = aeval t p := by
  let a := algebraMap k[X] (integralClosure k[X] E.toAffine.FunctionField) p
  have h := congrArg (fun b : coverCoordinateRing E 1 ⊥ false =>
    coordRingVal t (B := N) (unsignedQuadraticModelEquiv E j b))
    (baseNormalizationRingEquiv_square E p).symm
  exact h.trans ((coordRingVal_unsignedQuadraticModelEquiv_integralClosure E j a).trans
    (functionField_aeval_x E j p))

private theorem coordRingVal_signedQuadraticModelEquiv_polynomial (p : k[X]) :
    coordRingVal t (B := N) (ringMap (bot_le : (⊥ : IntermediateField (rationalBase k t) Ω) ≤ N)
      (signedQuadraticModelEquiv E j (signedBasePolynomialAlgEquiv E p))) = aeval t p := by
  let e := signedBasePolynomialAlgEquiv E
  let h : (⊥ : IntermediateField (rationalBase k t) Ω) ≤ N := bot_le
  let ht := transcendental_functionField_x E j
  change coordRingVal t (B := N) (ringMap h (constantExtensionLineEquiv ht (e.symm (e p)))) = _
  have he := congrArg (fun q : k[X] =>
    coordRingVal t (B := N) (ringMap h (constantExtensionLineEquiv ht q))) (e.symm_apply_apply p)
  exact he.trans ((coe_ringMap h (constantExtensionLineEquiv ht p)).trans
    (coe_constantExtensionLineEquiv ht p))

theorem quadraticModelEquiv_square (a : coverCoordinateRing E 1 ⊥ true) :
    unsignedQuadraticModelEquiv E j (signedNormalizationRingMap E 1 ⊥ a) =
      ringMap (bot_le : (⊥ : IntermediateField (rationalBase k t) Ω) ≤ N)
        (signedQuadraticModelEquiv E j a) := by
  obtain ⟨p, rfl⟩ := (signedBasePolynomialAlgEquiv E).surjective a
  exact (coordRingVal_injective t (B := N))
    ((coordRingVal_unsignedQuadraticModelEquiv_polynomial E j p).trans
      (coordRingVal_signedQuadraticModelEquiv_polynomial E j p).symm)

end FunctionField

end

end AbcAdaptation.Reference.Iut.Anabelian
