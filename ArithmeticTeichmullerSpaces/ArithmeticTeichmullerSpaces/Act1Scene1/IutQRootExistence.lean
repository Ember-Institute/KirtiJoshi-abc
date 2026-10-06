import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompletionSource

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

end IutTorsionQRootSource

end

end JoshiTeich.Act1Scene1
