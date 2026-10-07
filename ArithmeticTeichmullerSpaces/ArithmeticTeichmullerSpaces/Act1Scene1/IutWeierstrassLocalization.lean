/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutTorsionCardinality
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
source-id: IUT-COR312-WEIERSTRASS-LOCALIZATION
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/PointMap.lean` and
`refer/iut/Iut/Anabelian/LocalInputs.lean`.
fidelity: specializes the injective local additive map to actual Weierstrass points
using Mathlib's functorial affine-point map, then applies the existing torsion-cardinality
bound. Global rank-two torsion data and the local Tate uniformization remain inputs.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open WeierstrassCurve

noncomputable section

section PointMap

variable {k K : Type*} [Field k] [Field K]
variable {E : WeierstrassCurve k} [E.IsElliptic]

open scoped Classical

/-- The point map induced by a field homomorphism, with the target curve base changed. -/
def iutWeierstrassPointMap (f : k →+* K) :
    E.toAffine.Point →+ (E.map f).toAffine.Point := by
  letI := f.toAlgebra
  exact Affine.Point.map (W' := E) (S := k) (F := k) (K := K) (Algebra.ofId k K)

lemma iutWeierstrassPointMap_injective (f : k →+* K) :
    Function.Injective (iutWeierstrassPointMap (E := E) f) := by
  letI := f.toAlgebra
  exact Affine.Point.map_injective
    (W' := E) (S := k) (F := k) (K := K) (Algebra.ofId k K)

/-- The concrete localization map on points for a chosen global torsion basis. -/
def iutWeierstrassTorsionLocalMap {ell : ℕ}
    (f : k →+* K)
    (T : IutGlobalTorsionBasis E.toAffine.Point ell) :
    IutTorsionLocalMap T (E.map f).toAffine.Point where
  toLocal := iutWeierstrassPointMap (E := E) f
  injective := iutWeierstrassPointMap_injective (E := E) f

end PointMap

section SixTorsionRationalityContract

open scoped Classical

variable {F Fbar : Type*} [Field F] [NumberField F]
variable [Field Fbar] [Algebra F Fbar]
variable {E : WeierstrassCurve F} [E.IsElliptic]

/-- The `6`-torsion of the chosen extension is rational over `F`, as in IUT I,
Definition 3.1(b). This source condition does not require the extension to be algebraically
closed. -/
abbrev IutSixTorsionRational : Prop := by
  classical
  letI : DecidableEq F := Classical.decEq F
  letI : DecidableEq Fbar := Classical.decEq Fbar
  letI : (E.map (algebraMap F Fbar)).IsElliptic := by infer_instance
  exact ∀ P ∈ iutTorsion (E.map (algebraMap F Fbar)).toAffine.Point 6,
    P ∈ (iutWeierstrassPointMap (E := E) (algebraMap F Fbar)).range

end SixTorsionRationalityContract

section SixTorsionRationality

open scoped Classical

variable {F Fbar : Type*} [Field F] [NumberField F]
variable [Field Fbar] [Algebra F Fbar] [IsAlgClosed Fbar]
variable {E : WeierstrassCurve F} [E.IsElliptic]

/-- Rationality of the geometric `6`-torsion supplies the four base-field `2`-torsion
points used by the IUT local q-root argument. The three finite points come from the distinct
roots of the Weierstrass `2`-torsion cubic; the point at infinity supplies the fourth point. -/
theorem iutWeierstrass_four_global_two_torsion_points_of_six_torsion_rational
    (hsix : IutSixTorsionRational (F := F) (Fbar := Fbar) (E := E)) :
    Nonempty (Fin 4 ↪ ↥(iutTorsion E.toAffine.Point 2)) := by
  classical
  let f : F →+* Fbar := algebraMap F Fbar
  let Ebar : WeierstrassCurve Fbar := E.map f
  let W : WeierstrassCurve.Affine Fbar := Ebar.toAffine
  let C : Cubic Fbar := W.twoTorsionPolynomial
  haveI : CharZero Fbar := charZero_of_injective_algebraMap f.injective
  haveI : NeZero (2 : Fbar) := ⟨by exact two_ne_zero⟩
  haveI : W.IsElliptic := by dsimp [W, Ebar]; infer_instance
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  have ha : C.a ≠ 0 := by
    simp [C, WeierstrassCurve.twoTorsionPolynomial]
  have hsplit : C.toPoly.Splits := IsAlgClosed.splits C.toPoly
  have hdiscr : C.discr ≠ 0 := by
    rw [show C = W.twoTorsionPolynomial by rfl,
      WeierstrassCurve.twoTorsionPolynomial_discr]
    exact mul_ne_zero (by norm_num) hΔ
  let Cid : Cubic Fbar := Cubic.map (RingHom.id Fbar) C
  have hCid : Cid = C := by ext <;> simp [Cid, Cubic.map]
  let roots : Finset Fbar := Cid.roots.toFinset
  have hroots : roots.card = 3 := by
    simpa [roots] using
      (Cubic.card_roots_of_discr_ne_zero (P := C) (φ := RingHom.id Fbar) ha
        (by simpa using hsplit) hdiscr)
  obtain ⟨x₁, x₂, x₃, hx₁₂, hx₁₃, hx₂₃, hrootsEq⟩ := Finset.card_eq_three.mp hroots
  have hroot₁ : C.toPoly.IsRoot x₁ := by
    have hx : x₁ ∈ roots := by rw [hrootsEq]; simp
    change x₁ ∈ Cid.roots.toFinset at hx
    have hx' : x₁ ∈ Cid.toPoly.roots := Multiset.mem_toFinset.mp hx
    simpa [hCid] using Polynomial.isRoot_of_mem_roots hx'
  have hroot₂ : C.toPoly.IsRoot x₂ := by
    have hx : x₂ ∈ roots := by rw [hrootsEq]; simp
    change x₂ ∈ Cid.roots.toFinset at hx
    have hx' : x₂ ∈ Cid.toPoly.roots := Multiset.mem_toFinset.mp hx
    simpa [hCid] using Polynomial.isRoot_of_mem_roots hx'
  have hroot₃ : C.toPoly.IsRoot x₃ := by
    have hx : x₃ ∈ roots := by rw [hrootsEq]; simp
    change x₃ ∈ Cid.roots.toFinset at hx
    have hx' : x₃ ∈ Cid.toPoly.roots := Multiset.mem_toFinset.mp hx
    simpa [hCid] using Polynomial.isRoot_of_mem_roots hx'
  obtain ⟨y₁, hn₁, ht₁⟩ :=
    (Affine.Point.isRoot_twoTorsionPolynomial_iff (W := W) (show NeZero (2 : Fbar) from inferInstance)
      hΔ x₁).mp (by simpa [C] using hroot₁)
  obtain ⟨y₂, hn₂, ht₂⟩ :=
    (Affine.Point.isRoot_twoTorsionPolynomial_iff (W := W) (show NeZero (2 : Fbar) from inferInstance)
      hΔ x₂).mp (by simpa [C] using hroot₂)
  obtain ⟨y₃, hn₃, ht₃⟩ :=
    (Affine.Point.isRoot_twoTorsionPolynomial_iff (W := W) (show NeZero (2 : Fbar) from inferInstance)
      hΔ x₃).mp (by simpa [C] using hroot₃)
  let P₁ : W.Point := .some x₁ y₁ hn₁
  let P₂ : W.Point := .some x₂ y₂ hn₂
  let P₃ : W.Point := .some x₃ y₃ hn₃
  have hP₁two : 2 • P₁ = 0 := by simpa [P₁, two_nsmul] using ht₁
  have hP₂two : 2 • P₂ = 0 := by simpa [P₂, two_nsmul] using ht₂
  have hP₃two : 2 • P₃ = 0 := by simpa [P₃, two_nsmul] using ht₃
  have hP₁six : P₁ ∈ iutTorsion W.Point 6 := by
    rw [AddSubgroup.torsionBy.nsmul_iff]
    calc
      (6 : ℕ) • P₁ = 3 • (2 • P₁) := by rw [← mul_nsmul]
      _ = 0 := by simp [hP₁two]
  have hP₂six : P₂ ∈ iutTorsion W.Point 6 := by
    rw [AddSubgroup.torsionBy.nsmul_iff]
    calc
      (6 : ℕ) • P₂ = 3 • (2 • P₂) := by rw [← mul_nsmul]
      _ = 0 := by simp [hP₂two]
  have hP₃six : P₃ ∈ iutTorsion W.Point 6 := by
    rw [AddSubgroup.torsionBy.nsmul_iff]
    calc
      (6 : ℕ) • P₃ = 3 • (2 • P₃) := by rw [← mul_nsmul]
      _ = 0 := by simp [hP₃two]
  let pointMap := iutWeierstrassPointMap (E := E) f
  change (∀ P ∈ iutTorsion W.Point 6, P ∈ pointMap.range) at hsix
  obtain ⟨Q₁, hQ₁map⟩ := Set.mem_range.mp (hsix P₁ hP₁six)
  obtain ⟨Q₂, hQ₂map⟩ := Set.mem_range.mp (hsix P₂ hP₂six)
  obtain ⟨Q₃, hQ₃map⟩ := Set.mem_range.mp (hsix P₃ hP₃six)
  change pointMap Q₁ = P₁ at hQ₁map
  change pointMap Q₂ = P₂ at hQ₂map
  change pointMap Q₃ = P₃ at hQ₃map
  have hQ₁two : Q₁ ∈ iutTorsion E.toAffine.Point 2 := by
    rw [AddSubgroup.torsionBy.nsmul_iff]
    apply iutWeierstrassPointMap_injective (E := E) f
    calc
      pointMap (2 • Q₁) = 2 • pointMap Q₁ := map_nsmul _ _ _
      _ = 2 • P₁ := by rw [hQ₁map]
      _ = pointMap 0 := by rw [hP₁two, map_zero]
  have hQ₂two : Q₂ ∈ iutTorsion E.toAffine.Point 2 := by
    rw [AddSubgroup.torsionBy.nsmul_iff]
    apply iutWeierstrassPointMap_injective (E := E) f
    calc
      pointMap (2 • Q₂) = 2 • pointMap Q₂ := map_nsmul _ _ _
      _ = 2 • P₂ := by rw [hQ₂map]
      _ = pointMap 0 := by rw [hP₂two, map_zero]
  have hQ₃two : Q₃ ∈ iutTorsion E.toAffine.Point 2 := by
    rw [AddSubgroup.torsionBy.nsmul_iff]
    apply iutWeierstrassPointMap_injective (E := E) f
    calc
      pointMap (2 • Q₃) = 2 • pointMap Q₃ := map_nsmul _ _ _
      _ = 2 • P₃ := by rw [hQ₃map]
      _ = pointMap 0 := by rw [hP₃two, map_zero]
  let T := ↥(iutTorsion E.toAffine.Point 2)
  let Q₀ : T := ⟨0, by simp [iutTorsion]⟩
  let R₁ : T := ⟨Q₁, hQ₁two⟩
  let R₂ : T := ⟨Q₂, hQ₂two⟩
  let R₃ : T := ⟨Q₃, hQ₃two⟩
  have hQ₀₁ : (Q₀ : E.toAffine.Point) ≠ R₁ := by
    intro h
    have hm := congrArg pointMap h
    rw [map_zero, hQ₁map] at hm
    exact Affine.Point.some_ne_zero hn₁ hm.symm
  have hQ₀₂ : (Q₀ : E.toAffine.Point) ≠ R₂ := by
    intro h
    have hm := congrArg pointMap h
    rw [map_zero, hQ₂map] at hm
    exact Affine.Point.some_ne_zero hn₂ hm.symm
  have hQ₀₃ : (Q₀ : E.toAffine.Point) ≠ R₃ := by
    intro h
    have hm := congrArg pointMap h
    rw [map_zero, hQ₃map] at hm
    exact Affine.Point.some_ne_zero hn₃ hm.symm
  have hQ₁₂ : (R₁ : E.toAffine.Point) ≠ R₂ := by
    intro h
    have hm := congrArg pointMap h
    rw [hQ₁map, hQ₂map] at hm
    change Affine.Point.some x₁ y₁ hn₁ = Affine.Point.some x₂ y₂ hn₂ at hm
    exact hx₁₂ (Affine.Point.some.inj hm).1
  have hQ₁₃ : (R₁ : E.toAffine.Point) ≠ R₃ := by
    intro h
    have hm := congrArg pointMap h
    rw [hQ₁map, hQ₃map] at hm
    change Affine.Point.some x₁ y₁ hn₁ = Affine.Point.some x₃ y₃ hn₃ at hm
    exact hx₁₃ (Affine.Point.some.inj hm).1
  have hQ₂₃ : (R₂ : E.toAffine.Point) ≠ R₃ := by
    intro h
    have hm := congrArg pointMap h
    rw [hQ₂map, hQ₃map] at hm
    change Affine.Point.some x₂ y₂ hn₂ = Affine.Point.some x₃ y₃ hn₃ at hm
    exact hx₂₃ (Affine.Point.some.inj hm).1
  have hQ₀₁' : Q₀ ≠ R₁ := fun h => hQ₀₁ (congrArg Subtype.val h)
  have hQ₀₂' : Q₀ ≠ R₂ := fun h => hQ₀₂ (congrArg Subtype.val h)
  have hQ₀₃' : Q₀ ≠ R₃ := fun h => hQ₀₃ (congrArg Subtype.val h)
  have hQ₁₂' : R₁ ≠ R₂ := fun h => hQ₁₂ (congrArg Subtype.val h)
  have hQ₁₃' : R₁ ≠ R₃ := fun h => hQ₁₃ (congrArg Subtype.val h)
  have hQ₂₃' : R₂ ≠ R₃ := fun h => hQ₂₃ (congrArg Subtype.val h)
  let fourPoints : Fin 4 → T := fun i =>
    match i.val with
    | 0 => Q₀
    | 1 => R₁
    | 2 => R₂
    | _ => R₃
  have hfourPoints : Function.Injective fourPoints := by
    intro i j hij
    apply Fin.ext
    fin_cases i <;> fin_cases j <;>
      simp [fourPoints, hQ₀₁', hQ₀₁'.symm, hQ₀₂', hQ₀₂'.symm,
        hQ₀₃', hQ₀₃'.symm, hQ₁₂', hQ₁₂'.symm, hQ₁₃', hQ₁₃'.symm,
        hQ₂₃', hQ₂₃'.symm] at hij ⊢
  exact ⟨fourPoints, hfourPoints⟩

end SixTorsionRationality

section LocalCardinality

variable {k K : Type*} [Field k] [NormedField K]
variable {E : WeierstrassCurve k} [E.IsElliptic]

open scoped Classical

/-- A rank-two global torsion basis gives the local `ell²` lower bound under
Weierstrass base change and a Tate quotient uniformization. -/
theorem iutWeierstrass_local_torsion_card_lower_bound
    {ell : ℕ} (f : k →+* K)
    (T : IutGlobalTorsionBasis E.toAffine.Point ell)
    (S : IutTateQuotientUniformization K ((E.map f).toAffine.Point))
    (hEll : 0 < ell) :
    ell * ell ≤ Nat.card ↥(iutTorsion (E.map f).toAffine.Point ell) :=
  IutTorsionLocalMap.card_localTorsion_lower_bound T
    (iutWeierstrassTorsionLocalMap (E := E) f T) S hEll

/-- Any global lower bound on `ell`-torsion transfers through Weierstrass base change.
The map on points is injective, and the target torsion is finite by the Tate quotient. -/
theorem iutWeierstrass_local_torsion_card_lower_bound_of_global_card
    {ell : ℕ} (f : k →+* K)
    (S : IutTateQuotientUniformization K ((E.map f).toAffine.Point))
    (hEll : 0 < ell)
    (hGlobal : ell * ell ≤ Nat.card ↥(iutTorsion E.toAffine.Point ell)) :
    ell * ell ≤ Nat.card ↥(iutTorsion (E.map f).toAffine.Point ell) := by
  letI : NeZero ell := ⟨Nat.ne_of_gt hEll⟩
  haveI : Finite ↥(iutTorsion (E.map f).toAffine.Point ell) := S.finite_torsion
  let pointMap := iutWeierstrassPointMap (E := E) f
  have hmem : ∀ P : ↥(iutTorsion E.toAffine.Point ell),
      pointMap P.1 ∈ iutTorsion (E.map f).toAffine.Point ell := by
    intro P
    have hP := P.2
    rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
    rw [← map_nsmul, hP, map_zero]
  refine hGlobal.trans (Nat.card_le_card_of_injective
    (fun P : ↥(iutTorsion E.toAffine.Point ell) =>
      (⟨pointMap P.1, hmem P⟩ : ↥(iutTorsion (E.map f).toAffine.Point ell))) ?_)
  intro P Q h
  apply Subtype.ext
  exact iutWeierstrassPointMap_injective (E := E) f (congrArg Subtype.val h)

/-- Rational geometric `6`-torsion gives four distinct global `2`-torsion points.
Their images give the local cardinality bound, where finiteness follows from the Tate quotient. -/
theorem iutWeierstrass_local_two_torsion_card_lower_bound_of_six_torsion_rational
    {Fbar : Type*} [NumberField k] [Field Fbar] [Algebra k Fbar] [IsAlgClosed Fbar]
    (f : k →+* K)
    (S : IutTateQuotientUniformization K ((E.map f).toAffine.Point))
    (hsix : IutSixTorsionRational (F := k) (Fbar := Fbar) (E := E)) :
    4 ≤ Nat.card ↥(iutTorsion (E.map f).toAffine.Point 2) := by
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  haveI : Finite ↥(iutTorsion (E.map f).toAffine.Point 2) := S.finite_torsion
  obtain ⟨e⟩ := iutWeierstrass_four_global_two_torsion_points_of_six_torsion_rational
    (F := k) (Fbar := Fbar) (E := E) hsix
  let pointMap := iutWeierstrassPointMap (E := E) f
  have hmem (P : ↥(iutTorsion E.toAffine.Point 2)) :
      pointMap P.1 ∈ iutTorsion (E.map f).toAffine.Point 2 := by
    have hP := P.2
    rw [AddSubgroup.torsionBy.nsmul_iff] at hP ⊢
    rw [← map_nsmul, hP, map_zero]
  let localPoints : Fin 4 → ↥(iutTorsion (E.map f).toAffine.Point 2) :=
    fun i => ⟨pointMap (e i).1, hmem (e i)⟩
  have hinj : Function.Injective localPoints := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    apply iutWeierstrassPointMap_injective (E := E) f
    exact congrArg Subtype.val hij
  have hcard := Nat.card_le_card_of_injective localPoints hinj
  simpa using hcard

/-- Four global rational `2`-torsion points force a square root of the Tate parameter
after localization. This is the square-root input used by the IUT `2 ell`-root argument. -/
theorem iutWeierstrass_exists_square_root_of_global_two_torsion
    (f : k →+* K)
    (S : IutTateQuotientUniformization K ((E.map f).toAffine.Point))
    (htwo : 2 * 2 ≤ Nat.card ↥(iutTorsion E.toAffine.Point 2)) :
    ∃ s : K, s ^ 2 = (S.q : K) := by
  have hLocal := iutWeierstrass_local_torsion_card_lower_bound_of_global_card
    (E := E) f S (ell := 2) (by omega) htwo
  obtain ⟨u, m, hu⟩ := S.exists_root_class_values_of_torsion_card (ell := 2)
    (by omega) hLocal
  exact IutQRootExistence.exists_pow_eq_of_root_class_of_nonzero
    (show 0 < 2 by omega) (Units.ne_zero S.q) hu

/-- Rational geometric `6`-torsion supplies the four global `2`-torsion points needed to
derive a square root of the local Tate parameter. -/
theorem iutWeierstrass_exists_square_root_of_six_torsion_rational
    {Fbar : Type*} [NumberField k] [Field Fbar] [Algebra k Fbar] [IsAlgClosed Fbar]
    (f : k →+* K)
    (S : IutTateQuotientUniformization K ((E.map f).toAffine.Point))
    (hsix : IutSixTorsionRational (F := k) (Fbar := Fbar) (E := E)) :
    ∃ s : K, s ^ 2 = (S.q : K) := by
  have hLocal := iutWeierstrass_local_two_torsion_card_lower_bound_of_six_torsion_rational
    (E := E) (Fbar := Fbar) f S hsix
  obtain ⟨u, m, hu⟩ := S.exists_root_class_values_of_torsion_card (ell := 2)
    (by omega) hLocal
  exact IutQRootExistence.exists_pow_eq_of_root_class_of_nonzero
    (show 0 < 2 by omega) (Units.ne_zero S.q) hu

end LocalCardinality

universe uF uKt uFbar

section WeierstrassQRootSource

open scoped Classical

variable {F Kt : Type uF} [Field F] [NumberField F]
variable [Field Kt] [NumberField Kt] [Algebra F Kt]
variable {Fbar : Type uFbar} [Field Fbar] [Algebra F Fbar] [IsAlgClosed Fbar]
variable {ell : ℕ} {B : IutBaseQPilotSource F ell}
variable {E : WeierstrassCurve F} [E.IsElliptic]

/-- Assemble the IUT q-root source from a Weierstrass `ell`-torsion basis over `Kt` and
rational `2`-torsion over `F`. At each bad place, the local Tate quotient supplies the
uniformization; the square root is derived from the global `2`-torsion bound. -/
noncomputable def IutTorsionQRootSource.ofOverBaseBadWithCanonicalCompletionMap_ofWeierstrassTorsion
    (B : IutBaseQPilotSource F ell)
    (T : IutGlobalTorsionBasis
      (E.map (algebraMap F Kt)).toAffine.Point ell)
    (S : ∀ w : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite,
      IutTateQuotientUniformization (w.1.maximalIdeal.adicCompletion Kt)
        ((((E.map (algebraMap F Kt)).map
          (NumberField.FinitePlace.embedding w.1.maximalIdeal)).toAffine.Point)))
    (hsix : IutSixTorsionRational (F := F) (Fbar := Fbar) (E := E))
    (hEll : 0 < ell) (hodd : Odd ell)
    (hq : ∀ w : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite,
      ((S w).q : w.1.maximalIdeal.adicCompletion Kt) =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) w)
          (B.tateParameter (basePlaceOf (B := B) w))) :
    IutTorsionQRootSource F Kt ell B := by
  let E_Kt : WeierstrassCurve Kt := E.map (algebraMap F Kt)
  have hCard : ∀ w : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite,
      ell * ell ≤ Nat.card ↥(iutTorsion
        ((E_Kt.map (NumberField.FinitePlace.embedding w.1.maximalIdeal)).toAffine.Point)
        ell) := by
    intro w
    exact iutWeierstrass_local_torsion_card_lower_bound
      (E := E_Kt) (NumberField.FinitePlace.embedding w.1.maximalIdeal) T (S w) hEll
  let squareRoot : ∀ w : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite, w.1.maximalIdeal.adicCompletion Kt :=
    fun w => Classical.choose
      (iutWeierstrass_exists_square_root_of_six_torsion_rational
        (E := E)
        (Fbar := Fbar)
        ((NumberField.FinitePlace.embedding w.1.maximalIdeal).comp (algebraMap F Kt))
        (S w) hsix)
  have hsquareRoot : ∀ w : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite,
      squareRoot w ^ 2 =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) w)
          (B.tateParameter (basePlaceOf (B := B) w)) := by
    intro w
    exact (Classical.choose_spec
      (iutWeierstrass_exists_square_root_of_six_torsion_rational
        (E := E)
        (Fbar := Fbar)
        ((NumberField.FinitePlace.embedding w.1.maximalIdeal).comp (algebraMap F Kt))
        (S w) hsix)).trans (hq w)
  exact IutTorsionQRootSource.ofOverBaseBadWithCanonicalCompletionMap_ofTateUniformizationAndSquareRoot
    B (fun w => (E_Kt.map
      (NumberField.FinitePlace.embedding w.1.maximalIdeal)).toAffine.Point)
    S hEll hCard hq squareRoot hodd hsquareRoot

end WeierstrassQRootSource

end

end JoshiTeich.Act1Scene1
