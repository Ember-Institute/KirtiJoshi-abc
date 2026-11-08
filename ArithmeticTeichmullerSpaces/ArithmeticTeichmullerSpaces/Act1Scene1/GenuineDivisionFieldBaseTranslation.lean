import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineDivisionFieldTranslation
import Mathlib.FieldTheory.Normal.Basic

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); the actual division-point fields;
`GenuineDivisionFieldBaseNegation.lean`; Mathlib point-map functoriality and
`AlgEquiv.liftNormal` over the original Galois base.
fidelity: translation by an actual rational n-torsion point fixes the original
x-line base because n(Q_n+T)=nQ_n. The same automorphism lifts over that base
to the existing ambient closure, and sends the original Q_n to Q_n+T.
No arbitrary ambient extension over the constant field is used.
boundary: Scene1/Derived. This supplies actual translation automorphisms,
not a comparison of infinity primes with torsion classes or an AG.Cusp.
Original proofs adapted from the existing base-negation proof.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

private theorem divisionFieldTranslationEquiv_genericX
    (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) (hT : n • T = 0) :
    divisionFieldTranslationEquiv E n hn T
        (algebraMap (baseField E) (QField E n) ⟨xG E, xG_mem_baseField E⟩) =
      algebraMap (baseField E) (QField E n) ⟨xG E, xG_mem_baseField E⟩ := by
  let P := divisionFieldPoint E n hn
  let ι := divisionFieldInclusion E n
  let e := divisionFieldTranslationEquiv E n hn T
  let f := ι.comp e.toAlgHom
  have hmul : n • Qpt E n = genericPoint E := by
    rw [Qpt_eq_divSys E hn]
    exact nsmul_divSys E n hn
  have hbaseT : n • base E T = 0 := by
    rw [← map_nsmul, hT, map_zero]
  have hmapMul : Affine.Point.map (W' := E.toAffine) ι (n • P) = genericPoint E := by
    rw [map_nsmul, divisionFieldPoint_map, hmul]
  have hmapMulTrans : Affine.Point.map (W' := E.toAffine) f (n • P) = genericPoint E := by
    rw [map_nsmul, divisionFieldTranslationEquiv_pointMap,
      nsmul_add, hmul, hbaseT, add_zero]
  have hxmap (g : QField E n →ₐ[k] Ω E)
      (R : (E⁄(QField E n)).toAffine.Point) :
      ptX (Affine.Point.map (W' := E.toAffine) g R) = g (ptX R) := by
    cases R with
    | zero => exact (map_zero g).symm
    | some => rfl
  let xL : QField E n :=
    algebraMap (baseField E) (QField E n) ⟨xG E, xG_mem_baseField E⟩
  have hcoord : ptX (n • P) = xL := by
    apply Subtype.ext
    change ι (ptX (n • P)) = xG E
    rw [← hxmap, hmapMul]
    rfl
  apply Subtype.ext
  change f xL = xG E
  rw [← hcoord, ← hxmap, hmapMulTrans]
  rfl

/-- Torsion translation fixes the original Galois base pointwise. -/
theorem divisionFieldTranslationEquiv_baseField
    (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) (hT : n • T = 0)
    (a : baseField E) :
    divisionFieldTranslationEquiv E n hn T (algebraMap (baseField E) (QField E n) a) =
      algebraMap (baseField E) (QField E n) a := by
  let ι : baseField E →ₐ[k] QField E n :=
    IsScalarTower.toAlgHom k (baseField E) (QField E n)
  have heq : (divisionFieldTranslationEquiv E n hn T).toAlgHom.comp ι = ι := by
    apply IntermediateField.algHom_ext_of_eq_adjoin k (baseField_eq_xLine E)
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact divisionFieldTranslationEquiv_genericX E n hn T hT
  exact AlgHom.congr_fun heq a

/-- The actual translation, with its proved linearity over the original base. -/
def divisionFieldBaseTranslationEquiv
    (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) (hT : n • T = 0) :
    QField E n ≃ₐ[baseField E] QField E n :=
  { (divisionFieldTranslationEquiv E n hn T).toRingEquiv with
    commutes' := divisionFieldTranslationEquiv_baseField E n hn T hT }

/-- Lift over the original x-line base and retain the same chosen division point. -/
theorem exists_ambient_divisionPoint_translation
    (n : ℕ) (hn : 0 < n) (T : E.toAffine.Point) (hT : n • T = 0) :
    ∃ σ : Gal E, act E σ (Qpt E n) = Qpt E n + base E T := by
  let e := divisionFieldBaseTranslationEquiv E n hn T hT
  let σ : Gal E := e.liftNormal (Ω E)
  let P := divisionFieldPoint E n hn
  let ι := divisionFieldInclusion E n
  have hLiftPoint :
      act E σ (Affine.Point.map (W' := E.toAffine) ι P) =
        Affine.Point.map (W' := E.toAffine) (ι.comp (e.toAlgHom.restrictScalars k)) P := by
    cases P with
    | zero => exact map_zero _
    | some x y h =>
      change Affine.Point.some (σ (ι x)) (σ (ι y)) _ =
        Affine.Point.some (ι (e x)) (ι (e y)) _
      congr 1
      · exact e.liftNormal_commutes (Ω E) x
      · exact e.liftNormal_commutes (Ω E) y
  refine ⟨σ, ?_⟩
  rw [divisionFieldPoint_map] at hLiftPoint
  exact hLiftPoint.trans (divisionFieldTranslationEquiv_pointMap E n hn T)

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
