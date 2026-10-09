import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompletionSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutPlacesOver
import Mathlib.GroupTheory.Index

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe u

noncomputable section

/-!
source-id: IUT-COR312-QROOT-EXISTENCE-COMBINATION
source: `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Roots.lean`,
especially `exists_two_mul_add_mul_eq_one` and `exists_pow_two_mul_eq`.
fidelity: the pure group-theoretic root combination is ported independently of
elliptic-curve and torsion-cardinality data.  The completion constructor below
consumes an explicit square root and an explicit `ell`-th root of the canonical
Tate-parameter image; it does not construct either root from `InitialThetaData`
or a `TateFamily`.
boundary: Scene1/Derived
-/

namespace IutQRootExistence

lemma exists_two_mul_add_mul_eq_one {ell : ℕ} (hodd : Odd ell) :
    ∃ a b : ℤ, 2 * b + (ell : ℤ) * a = 1 := by
  have hcop : Nat.Coprime 2 ell := Nat.coprime_two_left.mpr hodd
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  refine ⟨y, x, ?_⟩
  push_cast at hxy
  linear_combination hxy

lemma exists_pow_eq_of_root_class
    {G : Type*} [CommGroup G] {q u : G} {ell : ℕ} {m : ℤ}
    (hu : u ^ ell = q ^ (1 + (ell : ℤ) * m)) :
    ∃ r : G, r ^ ell = q := by
  refine ⟨u * q ^ (-m), ?_⟩
  rw [mul_pow, hu, ← zpow_natCast, ← zpow_mul, ← zpow_add]
  convert zpow_one q using 2
  push_cast
  ring

lemma exists_pow_eq_of_root_class_of_nonzero
    {G : Type*} [CommGroupWithZero G] {q u : G} {ell : ℕ} {m : ℤ}
    (hEll : 0 < ell) (hq : q ≠ 0)
    (hu : u ^ ell = q ^ (1 + (ell : ℤ) * m)) :
    ∃ r : G, r ^ ell = q := by
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0, zero_pow (Nat.ne_of_gt hEll)] at hu
    exact (zpow_ne_zero _ hq) hu.symm
  let q' : Gˣ := Units.mk0 q hq
  let u' : Gˣ := Units.mk0 u hu0
  have hu' : u' ^ ell = q' ^ (1 + (ell : ℤ) * m) := by
    apply Units.ext
    simpa [u', q'] using hu
  obtain ⟨r', hr'⟩ := exists_pow_eq_of_root_class hu'
  exact ⟨r'.1, congrArg Units.val hr'⟩

/-!
The finite residue argument is the part of the IUT Tate-torsion proof that does
not depend on a particular elliptic-curve representation.  The caller supplies
the residue homomorphism, its kernel bound, and representatives of torsion
classes; the cardinality argument then forces the residue class `1` to occur.
-/
lemma exists_root_class_of_card
    {T U : Type*} [AddCommGroup T] [Finite T] [CommGroup U]
    {q : U} {ell : ℕ} (hEll : 0 < ell)
    (resid : T →+ ZMod ell)
    (hKernel : Nat.card resid.ker ≤ ell)
    (hCard : ell * ell ≤ Nat.card T)
    (rep : T → U) (expo : T → ℤ)
    (hRepPow : ∀ P, rep P ^ ell = q ^ expo P)
    (hResidRep : ∀ P, resid P = (expo P : ZMod ell)) :
    ∃ u : U, ∃ m : ℤ, u ^ ell = q ^ (1 + (ell : ℤ) * m) := by
  letI : NeZero ell := ⟨Nat.ne_of_gt hEll⟩
  have hRange : Nat.card resid.range ≤ ell := by
    calc
      Nat.card resid.range ≤ Nat.card (ZMod ell) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = ell := by simp
  have hKernelRange : Nat.card resid.ker * Nat.card resid.range = Nat.card T :=
    AddSubgroup.card_ker_mul_card_range resid
  have hEq : Nat.card resid.ker = ell ∧ Nat.card resid.range = ell := by
    have hMul : ell * ell ≤ Nat.card resid.ker * Nat.card resid.range := by
      rw [hKernelRange]
      exact hCard
    exact ⟨(by
      by_contra hne
      have hlt : Nat.card resid.ker < ell := lt_of_le_of_ne hKernel hne
      have hUpper : Nat.card resid.ker * Nat.card resid.range ≤
          Nat.card resid.ker * ell := Nat.mul_le_mul_left _ hRange
      have hStrict : Nat.card resid.ker * ell < ell * ell := by
        exact (Nat.mul_lt_mul_right hEll).2 hlt
      omega), (by
      by_contra hne
      have hlt : Nat.card resid.range < ell := lt_of_le_of_ne hRange hne
      have hUpper : Nat.card resid.ker * Nat.card resid.range ≤
          ell * Nat.card resid.range := Nat.mul_le_mul_right _ hKernel
      have hStrict : ell * Nat.card resid.range < ell * ell := by
        exact (Nat.mul_lt_mul_left hEll).2 hlt
      omega)⟩
  have hRangeTop : resid.range = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmod]
    exact hEq.2
  have hOne : (1 : ZMod ell) ∈ resid.range := by
    rw [hRangeTop]
    trivial
  obtain ⟨P, hP⟩ := hOne
  rw [hResidRep P, ← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub,
    ZMod.intCast_zmod_eq_zero_iff_dvd] at hP
  obtain ⟨m, hm⟩ := hP
  refine ⟨rep P, m, ?_⟩
  rw [hRepPow P]
  congr 1
  omega

lemma exists_pow_two_mul_eq {G : Type*} [CommGroup G] {q r s : G} {ell : ℕ}
    (hodd : Odd ell) (hr : r ^ ell = q) (hs : s ^ 2 = q) :
    ∃ x : G, x ^ (2 * ell) = q := by
  obtain ⟨a, b, hab⟩ := exists_two_mul_add_mul_eq_one hodd
  refine ⟨s ^ a * r ^ b, ?_⟩
  have h1 : (s ^ a) ^ (2 * ell) = q ^ ((ell : ℤ) * a) := by
    rw [← zpow_natCast, ← zpow_mul, ← hs, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  have h2 : (r ^ b) ^ (2 * ell) = q ^ (2 * b) := by
    rw [← zpow_natCast, ← zpow_mul, ← hr, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow, h1, h2, ← zpow_add, add_comm, hab, zpow_one]

lemma exists_pow_two_mul_eq_of_nonzero
    {G : Type*} [CommGroupWithZero G] {q r s : G} {ell : ℕ}
    (hodd : Odd ell) (hr : r ^ ell = q) (hs : s ^ 2 = q)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0) :
    ∃ x : G, x ^ (2 * ell) = q := by
  have hq : q ≠ 0 := by
    rw [← hr]
    exact pow_ne_zero ell hr0
  let q' : Gˣ := Units.mk0 q hq
  let r' : Gˣ := Units.mk0 r hr0
  let s' : Gˣ := Units.mk0 s hs0
  have hr' : r' ^ ell = q' := by
    apply Units.ext
    exact hr
  have hs' : s' ^ 2 = q' := by
    apply Units.ext
    exact hs
  obtain ⟨x, hx⟩ := exists_pow_two_mul_eq hodd hr' hs'
  refine ⟨x, ?_⟩
  exact congrArg Units.val hx

lemma ne_zero_of_pow_eq_of_pos
    {G : Type*} [MonoidWithZero G] {x q : G} {n : ℕ}
    (hn : 0 < n) (h : x ^ n = q) (hq : q ≠ 0) : x ≠ 0 := by
  intro hx
  rw [hx, zero_pow (Nat.ne_of_gt hn)] at h
  exact hq h.symm

end IutQRootExistence

namespace IutTorsionQRootSource

variable {F Kt : Type u} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
variable [Algebra F Kt] {ell : ℕ} {B : IutBaseQPilotSource F ell}

lemma canonical_tateParameter_image_ne_zero
    (B : IutBaseQPilotSource F ell)
    (v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite) :
    iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
        (B.tateParameter (basePlaceOf (B := B) v)) ≠ 0 :=
  (map_ne_zero _).2 (B.tateParameter_ne_zero (basePlaceOf (B := B) v))

noncomputable def ellRootOfRootClass
    (B : IutBaseQPilotSource F ell)
    (hEll : 0 < ell)
    (rootClass : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt)
    (rootClassExponent : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite, ℤ)
    (rootClass_pow_eq : ∀ v,
      rootClass v ^ ell =
        (iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v))) ^
            (1 + (ell : ℤ) * rootClassExponent v)) :
    ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt :=
  fun v => Classical.choose
    (IutQRootExistence.exists_pow_eq_of_root_class_of_nonzero hEll
      (canonical_tateParameter_image_ne_zero B v) (rootClass_pow_eq v))

lemma ellRootOfRootClass_pow_eq
    (B : IutBaseQPilotSource F ell)
    (hEll : 0 < ell)
    (rootClass : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt)
    (rootClassExponent : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite, ℤ)
    (rootClass_pow_eq : ∀ v,
      rootClass v ^ ell =
        (iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v))) ^
            (1 + (ell : ℤ) * rootClassExponent v))
    (v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite) :
    ellRootOfRootClass B hEll rootClass rootClassExponent rootClass_pow_eq v ^ ell =
      iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
        (B.tateParameter (basePlaceOf (B := B) v)) :=
  Classical.choose_spec (IutQRootExistence.exists_pow_eq_of_root_class_of_nonzero
    hEll (canonical_tateParameter_image_ne_zero B v) (rootClass_pow_eq v))

noncomputable def qrootOfSquareAndEllRoot
    (B : IutBaseQPilotSource F ell)
    (ellRoot squareRoot : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt)
    (hEll : 0 < ell) (hodd : Odd ell)
    (ellRoot_pow_eq : ∀ v,
      ellRoot v ^ ell =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v)))
    (squareRoot_pow_eq : ∀ v,
      squareRoot v ^ 2 =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v))) :
    ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt :=
  fun v => Classical.choose (IutQRootExistence.exists_pow_two_mul_eq_of_nonzero
    hodd (ellRoot_pow_eq v) (squareRoot_pow_eq v)
    (IutQRootExistence.ne_zero_of_pow_eq_of_pos hEll
      (ellRoot_pow_eq v) (canonical_tateParameter_image_ne_zero B v))
    (IutQRootExistence.ne_zero_of_pow_eq_of_pos (show 0 < 2 by decide)
      (squareRoot_pow_eq v) (canonical_tateParameter_image_ne_zero B v)))

lemma qrootOfSquareAndEllRoot_pow_eq
    (B : IutBaseQPilotSource F ell)
    (ellRoot squareRoot : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt)
    (hEll : 0 < ell) (hodd : Odd ell)
    (ellRoot_pow_eq : ∀ v,
      ellRoot v ^ ell =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v)))
    (squareRoot_pow_eq : ∀ v,
      squareRoot v ^ 2 =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v)))
    (v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite) :
    qrootOfSquareAndEllRoot B ellRoot squareRoot hEll hodd
        ellRoot_pow_eq squareRoot_pow_eq v ^ (2 * ell) =
      iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
        (B.tateParameter (basePlaceOf (B := B) v)) := by
  exact Classical.choose_spec (IutQRootExistence.exists_pow_two_mul_eq_of_nonzero
    hodd (ellRoot_pow_eq v) (squareRoot_pow_eq v)
    (IutQRootExistence.ne_zero_of_pow_eq_of_pos hEll
      (ellRoot_pow_eq v) (canonical_tateParameter_image_ne_zero B v))
    (IutQRootExistence.ne_zero_of_pow_eq_of_pos (show 0 < 2 by decide)
      (squareRoot_pow_eq v) (canonical_tateParameter_image_ne_zero B v)))

noncomputable def ofOverBaseBadWithCanonicalCompletionMap_ofRoots
    (B : IutBaseQPilotSource F ell)
    (ellRoot squareRoot : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt)
    (hEll : 0 < ell) (hodd : Odd ell)
    (ellRoot_pow_eq : ∀ v,
      ellRoot v ^ ell =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v)))
    (squareRoot_pow_eq : ∀ v,
      squareRoot v ^ 2 =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v))) :
    IutTorsionQRootSource F Kt ell B :=
  ofOverBaseBadWithCanonicalCompletionMap B
    (qrootOfSquareAndEllRoot B ellRoot squareRoot hEll hodd
      ellRoot_pow_eq squareRoot_pow_eq)
    (qrootOfSquareAndEllRoot_pow_eq B ellRoot squareRoot hEll hodd
      ellRoot_pow_eq squareRoot_pow_eq) hEll

noncomputable def ofOverBaseBadWithCanonicalCompletionMap_ofRootClassAndSquareRoot
    (B : IutBaseQPilotSource F ell)
    (rootClass : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt)
    (rootClassExponent : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite, ℤ)
    (squareRoot : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt)
      B.badPlaces B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt)
    (hEll : 0 < ell) (hodd : Odd ell)
    (rootClass_pow_eq : ∀ v,
      rootClass v ^ ell =
        (iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v))) ^
            (1 + (ell : ℤ) * rootClassExponent v))
    (squareRoot_pow_eq : ∀ v,
      squareRoot v ^ 2 =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v))) :
    IutTorsionQRootSource F Kt ell B :=
  ofOverBaseBadWithCanonicalCompletionMap_ofRoots B
    (ellRootOfRootClass B hEll rootClass rootClassExponent rootClass_pow_eq)
    squareRoot hEll hodd
    (ellRootOfRootClass_pow_eq B hEll rootClass rootClassExponent rootClass_pow_eq)
    squareRoot_pow_eq

end IutTorsionQRootSource

end

end JoshiTeich.Act1Scene1
