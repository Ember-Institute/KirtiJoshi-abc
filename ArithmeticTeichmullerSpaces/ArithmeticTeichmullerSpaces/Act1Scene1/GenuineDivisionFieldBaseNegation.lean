import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineDivisionFieldNegation
import Mathlib.FieldTheory.Normal.Basic

/-!
source-id: JT-SCENE1-GENUINE-DIVISION-FIELD-BASE-NEGATION
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib functorial group law on Weierstrass points and `AlgEquiv.liftNormal`.
fidelity: original proofs that the existing division-field negation fixes the
original x-line base, and extends over that base to the same ambient closure.
The extension negates the same chosen division point at every positive level.
boundary: Scene1/Derived. No etale fundamental-group comparison, Cartesian
orbicurve covering, core, theta-root model or geometry producer is constructed.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

universe u
open WeierstrassCurve Polynomial
open scoped Classical
noncomputable section

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

private theorem divisionFieldNegationEquiv_genericX (n : ℕ) (hn : 0 < n) :
    divisionFieldNegationEquiv E n hn
        (algebraMap (baseField E) (QField E n) ⟨xG E, xG_mem_baseField E⟩) =
      algebraMap (baseField E) (QField E n) ⟨xG E, xG_mem_baseField E⟩ := by
  have hQne : Qpt E n ≠ 0 := by
    rw [Qpt_eq_divSys E hn]
    exact divSys_ne_zero E n hn
  have hmul : n • Qpt E n = genericPoint E := by
    rw [Qpt_eq_divSys E hn]
    exact nsmul_divSys E n hn
  rcases hQ : Qpt E n with _ | ⟨x, y, hns⟩
  · exact False.elim (hQne hQ)
  let L : IntermediateField k (Ω E) := (QField E n).restrictScalars k
  have hx : x ∈ L := by
    have h : ptX (Qpt E n) ∈ QField E n := IntermediateField.subset_adjoin (baseField E)
      {ptX (Qpt E n), ptY (Qpt E n)} (by simp : ptX (Qpt E n) ∈ _)
    rw [hQ] at h
    exact h
  have hy : y ∈ L := by
    have h : ptY (Qpt E n) ∈ QField E n := IntermediateField.subset_adjoin (baseField E)
      {ptX (Qpt E n), ptY (Qpt E n)} (by simp : ptY (Qpt E n) ∈ _)
    rw [hQ] at h
    exact h
  let px : L := ⟨x, hx⟩
  let py : L := ⟨y, hy⟩
  let ι : L →ₐ[k] Ω E := IsScalarTower.toAlgHom k L (Ω E)
  let e := divisionFieldNegationEquiv E n hn
  let f : L →ₐ[k] Ω E := ι.comp e.toAlgHom
  have hnsL : (E⁄L).toAffine.Nonsingular px py :=
    (E.toAffine.baseChange_nonsingular (f := ι) ι.injective px py).mp hns
  let P : (E⁄L).toAffine.Point := Affine.Point.some px py hnsL
  have hmapP : Affine.Point.map (W' := E.toAffine) ι P = Qpt E n := by
    rw [hQ]
    rfl
  have hmapNeg : Affine.Point.map (W' := E.toAffine) f P = -Qpt E n := by
    rw [hQ]
    change Affine.Point.some (f px) (f py) _ = -Affine.Point.some x y hns
    rw [Affine.Point.neg_some]
    congr 1
    · change ((divisionFieldNegationEquiv E n hn ⟨x, hx⟩ : QField E n) : Ω E) = x
      simpa only [hQ, ptX] using divisionFieldNegationEquiv_X E n hn
    · change ((divisionFieldNegationEquiv E n hn ⟨y, hy⟩ : QField E n) : Ω E) =
        -y - algebraMap k (Ω E) E.a₁ * x - algebraMap k (Ω E) E.a₃
      simpa only [hQ, ptX, ptY, Affine.negY, baseChange, map_a₁, map_a₃] using
        divisionFieldNegationEquiv_Y E n hn
  have hmapMul : Affine.Point.map (W' := E.toAffine) ι (n • P) = genericPoint E := by
    rw [map_nsmul, hmapP, hmul]
  have hmapMulNeg : Affine.Point.map (W' := E.toAffine) f (n • P) =
      -genericPoint E := by
    rw [map_nsmul, hmapNeg, smul_neg, hmul]
  have hxmap (g : L →ₐ[k] Ω E) (R : (E⁄L).toAffine.Point) :
      ptX (Affine.Point.map (W' := E.toAffine) g R) = g (ptX R) := by
    cases R with
    | zero => exact (map_zero g).symm
    | some => rfl
  let xL : L := ⟨xG E, (QField E n).algebraMap_mem ⟨xG E, xG_mem_baseField E⟩⟩
  have hcoord : ptX (n • P) = xL := by
    apply Subtype.ext
    change ι (ptX (n • P)) = xG E
    rw [← hxmap, hmapMul]
    rfl
  apply Subtype.ext
  change f xL = xG E
  rw [← hcoord, ← hxmap, hmapMulNeg]
  rfl

/-- The existing division-field negation fixes the original Galois base pointwise. -/
theorem divisionFieldNegationEquiv_baseField (n : ℕ) (hn : 0 < n)
    (a : baseField E) :
    divisionFieldNegationEquiv E n hn
        (algebraMap (baseField E) (QField E n) a) =
      algebraMap (baseField E) (QField E n) a := by
  let ι : baseField E →ₐ[k] QField E n :=
    IsScalarTower.toAlgHom k (baseField E) (QField E n)
  have heq : (divisionFieldNegationEquiv E n hn).toAlgHom.comp ι = ι := by
    apply IntermediateField.algHom_ext_of_eq_adjoin k (baseField_eq_xLine E)
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact divisionFieldNegationEquiv_genericX E n hn
  exact AlgHom.congr_fun heq a

/-- The original negation, with its proved linearity over the original Galois base. -/
def divisionFieldBaseNegationEquiv (n : ℕ) (hn : 0 < n) :
    QField E n ≃ₐ[baseField E] QField E n :=
  { (divisionFieldNegationEquiv E n hn).toRingEquiv with
    commutes' := divisionFieldNegationEquiv_baseField E n hn }

/-- Normal lifting over the actual x-line base negates the same chosen division point. -/
theorem exists_ambient_divisionPoint_negation (n : ℕ) (hn : 0 < n) :
    ∃ σ : Gal E, act E σ (Qpt E n) = -Qpt E n := by
  let e := divisionFieldBaseNegationEquiv E n hn
  let σ : Gal E := e.liftNormal (Ω E)
  refine ⟨σ, ?_⟩
  have hx : ptX (Qpt E n) ∈ QField E n :=
    IntermediateField.subset_adjoin _ _ (by simp)
  have hy : ptY (Qpt E n) ∈ QField E n :=
    IntermediateField.subset_adjoin _ _ (by simp)
  have hσx : σ (ptX (Qpt E n)) = ptX (Qpt E n) := by
    calc
      σ (ptX (Qpt E n)) =
          ((e ⟨ptX (Qpt E n), hx⟩ : QField E n) : Ω E) :=
        e.liftNormal_commutes (Ω E) ⟨ptX (Qpt E n), hx⟩
      _ = ptX (Qpt E n) := divisionFieldNegationEquiv_X E n hn
  have hσy : σ (ptY (Qpt E n)) =
      -ptY (Qpt E n) - algebraMap k (Ω E) E.a₁ * ptX (Qpt E n) -
        algebraMap k (Ω E) E.a₃ := by
    calc
      σ (ptY (Qpt E n)) =
          ((e ⟨ptY (Qpt E n), hy⟩ : QField E n) : Ω E) :=
        e.liftNormal_commutes (Ω E) ⟨ptY (Qpt E n), hy⟩
      _ = _ := divisionFieldNegationEquiv_Y E n hn
  rcases hQ : Qpt E n with _ | ⟨x, y, hns⟩
  · exact map_zero _
  · change Affine.Point.some (σ x) (σ y) _ = -Affine.Point.some x y hns
    rw [Affine.Point.neg_some]
    congr 1
    · simpa only [hQ, ptX] using hσx
    · simpa only [hQ, ptX, ptY, Affine.negY, baseChange, map_a₁, map_a₃] using hσy

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
