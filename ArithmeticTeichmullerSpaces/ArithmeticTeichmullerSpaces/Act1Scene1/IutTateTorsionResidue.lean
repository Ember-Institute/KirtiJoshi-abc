/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutQRootExistence
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.Index

/-!
source-id: IUT-COR312-TATE-TORSION-RESIDUE
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/TateStructure.lean` and
`refer/iut/Iut/Anabelian/TateTorsion.lean`.
fidelity: ports the group-theoretic part of the Tate uniformization and its
residue-map proof to an abstract additive target. The elliptic-curve coordinate
pinning and the `TateCurvesTheta` dependency are not copied. A real source must
still supply the quotient uniformization and the full-torsion cardinality bound.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

universe u v

noncomputable section

abbrev iutTorsion (A : Type v) [AddCommGroup A] (ell : ℕ) : AddSubgroup A :=
  AddSubgroup.torsionBy A ell

/-- The group-theoretic data used by the IUT Tate-torsion argument. -/
structure IutTateQuotientUniformization (K : Type u) [NormedField K]
    (A : Type v) [AddCommGroup A] where
  q : Kˣ
  q_norm_lt_one : ‖(q : K)‖ < 1
  iso : Additive (Kˣ ⧸ Subgroup.zpowers q) ≃+ A

namespace IutTateQuotientUniformization

variable {K : Type u} [NormedField K] {A : Type v} [AddCommGroup A]
variable (S : IutTateQuotientUniformization K A)

def ofUnit (u : Kˣ) : A := S.iso (Additive.ofMul (QuotientGroup.mk u))

lemma ofUnit_mul (u v : Kˣ) : S.ofUnit (u * v) = S.ofUnit u + S.ofUnit v := by
  unfold ofUnit
  rw [← map_add]
  rfl

lemma ofUnit_one : S.ofUnit 1 = 0 := by
  unfold ofUnit
  rw [← map_zero S.iso]
  rfl

lemma ofUnit_inv (u : Kˣ) : S.ofUnit u⁻¹ = -S.ofUnit u := by
  rw [eq_neg_iff_add_eq_zero, ← S.ofUnit_mul, inv_mul_cancel, S.ofUnit_one]

lemma ofUnit_eq_iff (u v : Kˣ) :
    S.ofUnit u = S.ofUnit v ↔ ∃ n : ℤ, v = S.q ^ n * u := by
  unfold ofUnit
  rw [S.iso.injective.eq_iff, Additive.ofMul.injective.eq_iff, QuotientGroup.eq]
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn, mul_comm, mul_inv_cancel_left]⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn, mul_comm (S.q ^ n) u, inv_mul_cancel_left]⟩

lemma ofUnit_eq_zero_iff (u : Kˣ) :
    S.ofUnit u = 0 ↔ ∃ n : ℤ, u = S.q ^ n := by
  rw [← S.ofUnit_one, S.ofUnit_eq_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_right hn.symm
  · rintro ⟨n, rfl⟩
    exact ⟨-n, by rw [zpow_neg, inv_mul_cancel]⟩

lemma ofUnit_surjective : Function.Surjective S.ofUnit := fun P => by
  obtain ⟨a, ha⟩ := S.iso.surjective P
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  exact ⟨u, by unfold ofUnit; rw [hu]; simpa using ha⟩

lemma q_zpow_injective : Function.Injective fun n : ℤ => S.q ^ n := by
  intro a b h
  have h' : ‖((S.q ^ a : Kˣ) : K)‖ = ‖((S.q ^ b : Kˣ) : K)‖ :=
    congrArg (fun x : Kˣ => ‖(x : K)‖) h
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, norm_zpow, norm_zpow] at h'
  exact zpow_right_injective₀
    (norm_pos_iff.mpr (Units.ne_zero S.q)) S.q_norm_lt_one.ne h'

lemma nsmul_ofUnit (n : ℕ) (u : Kˣ) :
    n • S.ofUnit u = S.ofUnit (u ^ n) := by
  unfold ofUnit
  rw [← map_nsmul]
  rfl

lemma ofUnit_mem_torsionBy_iff (ell : ℕ) (u : Kˣ) :
    S.ofUnit u ∈ AddSubgroup.torsionBy A ell ↔ ∃ n : ℤ, u ^ ell = S.q ^ n := by
  rw [AddSubgroup.torsionBy.nsmul_iff, S.nsmul_ofUnit, S.ofUnit_eq_zero_iff]

lemma exists_rep (ell : ℕ) (P : ↥(iutTorsion A ell)) :
    ∃ u : Kˣ, S.ofUnit u = P ∧ ∃ n : ℤ, u ^ ell = S.q ^ n := by
  obtain ⟨u, hu⟩ := S.ofUnit_surjective P.1
  exact ⟨u, hu, (S.ofUnit_mem_torsionBy_iff ell u).mp (hu ▸ P.2)⟩

def rep (ell : ℕ) (P : ↥(iutTorsion A ell)) : Kˣ :=
  (S.exists_rep ell P).choose

lemma ofUnit_rep (ell : ℕ) (P : ↥(iutTorsion A ell)) :
    S.ofUnit (S.rep ell P) = P :=
  (S.exists_rep ell P).choose_spec.1

def expo (ell : ℕ) (P : ↥(iutTorsion A ell)) : ℤ :=
  (S.exists_rep ell P).choose_spec.2.choose

lemma rep_pow (ell : ℕ) (P : ↥(iutTorsion A ell)) :
    S.rep ell P ^ ell = S.q ^ S.expo ell P :=
  (S.exists_rep ell P).choose_spec.2.choose_spec

lemma expo_congr (ell : ℕ) {u v : Kˣ} {n m : ℤ}
    (huv : S.ofUnit u = S.ofUnit v)
    (hu : u ^ ell = S.q ^ n) (hv : v ^ ell = S.q ^ m) :
    (m : ZMod ell) = n := by
  obtain ⟨j, hj⟩ := (S.ofUnit_eq_iff u v).mp huv
  have h : S.q ^ m = S.q ^ (j * ell + n) := by
    rw [← hv, hj, mul_pow, hu, ← zpow_natCast, ← zpow_mul, ← zpow_add]
  have hm := S.q_zpow_injective h
  rw [hm]
  push_cast
  simp

def resid (ell : ℕ) : ↥(iutTorsion A ell) →+ ZMod ell where
  toFun P := (S.expo ell P : ZMod ell)
  map_zero' := by
    obtain ⟨j, hj⟩ := (S.ofUnit_eq_zero_iff (S.rep ell 0)).mp (S.ofUnit_rep ell 0)
    have h : S.q ^ S.expo ell 0 = S.q ^ (j * ell) := by
      rw [← S.rep_pow, hj, ← zpow_natCast, ← zpow_mul]
    have := S.q_zpow_injective h
    simp [this]
  map_add' P Q := by
    have h : S.ofUnit (S.rep ell (P + Q)) =
        S.ofUnit (S.rep ell P * S.rep ell Q) := by
      rw [S.ofUnit_mul, S.ofUnit_rep, S.ofUnit_rep, S.ofUnit_rep]
      rfl
    have hExpo := S.expo_congr ell h (S.rep_pow ell (P + Q))
      (by rw [mul_pow, S.rep_pow, S.rep_pow, ← zpow_add])
    simp only [Int.cast_add] at hExpo
    exact hExpo.symm

lemma resid_apply (ell : ℕ) (P : ↥(iutTorsion A ell)) :
    S.resid ell P = (S.expo ell P : ZMod ell) := rfl

lemma resid_ofUnit (ell : ℕ) {u : Kˣ} {n : ℤ}
    (hu : u ^ ell = S.q ^ n) (hP : S.ofUnit u ∈ iutTorsion A ell) :
    S.resid ell ⟨S.ofUnit u, hP⟩ = (n : ZMod ell) := by
  rw [S.resid_apply]
  exact S.expo_congr ell (S.ofUnit_rep ell ⟨S.ofUnit u, hP⟩).symm hu
    (S.rep_pow ell _)

def graphLine (ell : ℕ) : AddSubgroup A where
  carrier := {P | ∃ ζ : Kˣ, ζ ^ ell = 1 ∧ S.ofUnit ζ = P}
  zero_mem' := ⟨1, one_pow ell, S.ofUnit_one⟩
  add_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u * v, by rw [mul_pow, hu, hv, one_mul], S.ofUnit_mul u v⟩
  neg_mem' := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u⁻¹, by rw [inv_pow, hu, inv_one], S.ofUnit_inv u⟩

lemma resid_eq_zero_iff (ell : ℕ) (P : ↥(iutTorsion A ell)) :
    S.resid ell P = 0 ↔ (P : A) ∈ S.graphLine ell := by
  constructor
  · intro h
    rw [S.resid_apply] at h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨j, hj⟩ := h
    refine ⟨S.rep ell P * (S.q ^ j)⁻¹, ?_, ?_⟩
    · rw [mul_pow, S.rep_pow, hj, inv_pow, ← zpow_natCast, ← zpow_mul,
        mul_comm (j : ℤ), mul_inv_cancel]
    · rw [S.ofUnit_mul, S.ofUnit_rep,
        (S.ofUnit_eq_zero_iff (S.q ^ j)⁻¹).mpr ⟨-j, by rw [zpow_neg]⟩,
        add_zero]
  · rintro ⟨ζ, hζ, hζP⟩
    have h := S.expo_congr ell (hζP.trans (S.ofUnit_rep ell P).symm)
      (by rw [hζ, zpow_zero]) (S.rep_pow ell P)
    rw [S.resid_apply, h]
    simp

variable {ell : ℕ} [NeZero ell]

omit [NeZero ell] in
lemma graphLine_le_torsion : S.graphLine ell ≤ iutTorsion A ell := by
  rintro _ ⟨ζ, hζ, rfl⟩
  rw [AddSubgroup.torsionBy.nsmul_iff, S.nsmul_ofUnit, hζ, S.ofUnit_one]

omit [NeZero ell] in
lemma ofUnit_rootsOfUnity_surjective :
    Function.Surjective (fun ζ : rootsOfUnity ell K =>
      (⟨S.ofUnit ζ.1,
        ⟨ζ.1, (mem_rootsOfUnity ell ζ.1).mp ζ.2, rfl⟩⟩ : ↥(S.graphLine ell))) := by
  rintro ⟨P, ζ, hζ, rfl⟩
  exact ⟨⟨ζ, (mem_rootsOfUnity ell ζ).mpr hζ⟩, rfl⟩

instance finite_graphLine : Finite ↥(S.graphLine ell) :=
  Finite.of_surjective _ S.ofUnit_rootsOfUnity_surjective

lemma card_graphLine_le : Nat.card ↥(S.graphLine ell) ≤ ell :=
  (Nat.card_le_card_of_surjective _ S.ofUnit_rootsOfUnity_surjective).trans
    (card_rootsOfUnity (R := K) (k := ell))

omit [NeZero ell] in
lemma resid_ker : (S.resid ell).ker =
    (S.graphLine ell).addSubgroupOf (iutTorsion A ell) := by
  ext P
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, S.resid_eq_zero_iff]

omit [NeZero ell] in
lemma card_torsion_eq : Nat.card ↥(iutTorsion A ell) =
    Nat.card ↥(S.graphLine ell) * Nat.card ↥(S.resid ell).range := by
  rw [← AddSubgroup.card_mul_index (S.resid ell).ker,
    AddSubgroup.index_eq_card, S.resid_ker]
  congr 1
  · exact Nat.card_congr
      (AddSubgroup.addSubgroupOfEquivOfLe S.graphLine_le_torsion).toEquiv
  · rw [← S.resid_ker]
    exact Nat.card_congr
      (QuotientAddGroup.quotientKerEquivRange (S.resid ell)).toEquiv

lemma card_range_le : Nat.card ↥(S.resid ell).range ≤ ell :=
  (Nat.card_le_card_of_injective _ Subtype.val_injective).trans (by
    rw [Nat.card_zmod])

include S in
lemma finite_torsion : Finite ↥(iutTorsion A ell) := by
  apply Nat.finite_of_card_ne_zero
  rw [S.card_torsion_eq]
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

lemma resid_ker_card_le : Nat.card (S.resid ell).ker ≤ ell := by
  rw [S.resid_ker]
  calc
    Nat.card ↥((S.graphLine ell).addSubgroupOf (iutTorsion A ell)) =
        Nat.card ↥(S.graphLine ell) :=
      Nat.card_congr
        (AddSubgroup.addSubgroupOfEquivOfLe S.graphLine_le_torsion).toEquiv
    _ ≤ ell := S.card_graphLine_le

omit [NeZero ell] in
lemma exists_root_class_of_torsion_card
    (hEll : 0 < ell)
    (hCard : ell * ell ≤ Nat.card ↥(iutTorsion A ell)) :
    ∃ u : Kˣ, ∃ m : ℤ, u ^ ell = S.q ^ (1 + (ell : ℤ) * m) := by
  letI : NeZero ell := ⟨Nat.ne_of_gt hEll⟩
  letI : Finite ↥(iutTorsion A ell) := S.finite_torsion
  exact IutQRootExistence.exists_root_class_of_card hEll (S.resid ell)
    S.resid_ker_card_le hCard (S.rep ell) (S.expo ell) (S.rep_pow ell)
    (S.resid_apply ell)

lemma exists_root_class_values_of_torsion_card
    (hEll : 0 < ell)
    (hCard : ell * ell ≤ Nat.card ↥(iutTorsion A ell)) :
    ∃ u : K, ∃ m : ℤ, u ^ ell = (S.q : K) ^ (1 + (ell : ℤ) * m) := by
  obtain ⟨u, m, hu⟩ := S.exists_root_class_of_torsion_card hEll hCard
  refine ⟨u, m, ?_⟩
  simpa using congrArg (fun x : Kˣ => (x : K)) hu

end IutTateQuotientUniformization

namespace IutTorsionQRootSource

universe uA

variable {F Kt : Type u} [Field F] [NumberField F]
variable [Field Kt] [NumberField Kt] [Algebra F Kt]
variable {ell : ℕ} {B : IutBaseQPilotSource F ell}

lemma exists_root_class_at_place_of_tate_uniformization
    (B : IutBaseQPilotSource F ell)
    (w : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite)
    (E : Type uA) [AddCommGroup E]
    (S : IutTateQuotientUniformization (w.1.maximalIdeal.adicCompletion Kt) E)
    (hEll : 0 < ell)
    (hCard : ell * ell ≤ Nat.card ↥(iutTorsion E ell))
    (hq : (S.q : w.1.maximalIdeal.adicCompletion Kt) =
      iutEmbedCompletion (basePlaceOf_liesOver (B := B) w)
        (B.tateParameter (basePlaceOf (B := B) w))) :
    ∃ u : w.1.maximalIdeal.adicCompletion Kt, ∃ m : ℤ,
      u ^ ell =
        (iutEmbedCompletion (basePlaceOf_liesOver (B := B) w)
          (B.tateParameter (basePlaceOf (B := B) w))) ^
            (1 + (ell : ℤ) * m) := by
  letI : NeZero ell := ⟨Nat.ne_of_gt hEll⟩
  obtain ⟨u, m, hu⟩ := S.exists_root_class_values_of_torsion_card hEll hCard
  exact ⟨u, m, by rw [← hq]; exact hu⟩

section Family

variable (B : IutBaseQPilotSource F ell)
variable (E : iutBadPlacesOverFinset (k := F) (K := Kt)
  B.badPlaces B.badPlaces_finite → Type uA)
variable [∀ w, AddCommGroup (E w)]
variable (S : ∀ w : iutBadPlacesOverFinset (k := F) (K := Kt)
  B.badPlaces B.badPlaces_finite,
    IutTateQuotientUniformization (w.1.maximalIdeal.adicCompletion Kt) (E w))
variable (hEll : 0 < ell)
variable (hCard : ∀ w, ell * ell ≤ Nat.card ↥(iutTorsion (E w) ell))
variable (hq : ∀ w,
  ((S w).q : w.1.maximalIdeal.adicCompletion Kt) =
    iutEmbedCompletion (basePlaceOf_liesOver (B := B) w)
      (B.tateParameter (basePlaceOf (B := B) w)))

include E S hEll hCard hq in
lemma rootClass_exists
    (w : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite) :
    ∃ u : w.1.maximalIdeal.adicCompletion Kt, ∃ m : ℤ,
      u ^ ell =
        (iutEmbedCompletion (basePlaceOf_liesOver (B := B) w)
          (B.tateParameter (basePlaceOf (B := B) w))) ^
            (1 + (ell : ℤ) * m) :=
  exists_root_class_at_place_of_tate_uniformization B w (E w) (S w)
    hEll (hCard w) (hq w)

include E S hEll hCard hq in
noncomputable def rootClass :
    ∀ w : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite, w.1.maximalIdeal.adicCompletion Kt :=
  fun w => Classical.choose (rootClass_exists B E S hEll hCard hq w)

include E S hEll hCard hq in
noncomputable def rootClassExponent :
    ∀ _w : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite, ℤ :=
  fun w => Classical.choose (Classical.choose_spec
    (rootClass_exists B E S hEll hCard hq w))

lemma rootClass_pow_eq
    (w : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite) :
    rootClass B E S hEll hCard hq w ^ ell =
      (iutEmbedCompletion (basePlaceOf_liesOver (B := B) w)
        (B.tateParameter (basePlaceOf (B := B) w))) ^
          (1 + (ell : ℤ) * rootClassExponent B E S hEll hCard hq w) := by
  exact Classical.choose_spec (Classical.choose_spec
    (rootClass_exists B E S hEll hCard hq w))

include E S hEll hCard hq in
noncomputable def ofOverBaseBadWithCanonicalCompletionMap_ofTateUniformizationAndSquareRoot
    (squareRoot : ∀ w : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite, w.1.maximalIdeal.adicCompletion Kt)
    (hodd : Odd ell)
    (squareRoot_pow_eq : ∀ w,
      squareRoot w ^ 2 =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) w)
          (B.tateParameter (basePlaceOf (B := B) w))) :
    IutTorsionQRootSource F Kt ell B :=
  ofOverBaseBadWithCanonicalCompletionMap_ofRootClassAndSquareRoot B
    (rootClass B E S hEll hCard hq)
    (rootClassExponent B E S hEll hCard hq) squareRoot hEll hodd
    (rootClass_pow_eq B E S hEll hCard hq) squareRoot_pow_eq

end Family

end IutTorsionQRootSource

end

end JoshiTeich.Act1Scene1
