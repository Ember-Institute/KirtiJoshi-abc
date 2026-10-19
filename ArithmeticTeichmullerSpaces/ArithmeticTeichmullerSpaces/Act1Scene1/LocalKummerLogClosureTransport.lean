import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerRationalClosureTransport
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerSaturatedTopology

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-LOG-CLOSURE-TRANSPORT
source: Joshi I ss:distinct-kummer-theories/pr:galois-cohomology-and-teich
(1588--1632); III principal-unit classes and logarithms (3190--3236).
fidelity: natural preferred-closure transport maps actual principal-unit
Kummer classes to the same base units, preserves their image and p-saturation,
and commutes with the original ordinary logarithm and its inverse. Both
subspace topologies remain the original ones. Integral-lift existence is
preserved through the original integral/rational coefficient comparison.
Fixed base field; no H1_e/BK or arbitrary holomorphoid transport asserted.
Original proofs, no reference copy; Prologue-R5 unchanged.
-/
namespace JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k]
variable {Ω Ξ : Type v} [Field Ω] [Field Ξ] [Algebra k Ω] [Algebra k Ξ]
variable [Algebra.IsIntegral k Ω] [IsGalois k Ω] [CharZero Ω] [IsAlgClosed Ω]
variable [Algebra.IsIntegral k Ξ] [IsGalois k Ξ] [CharZero Ξ] [IsAlgClosed Ξ]
variable (e : Ω ≃ₐ[k] Ξ) (p : ℕ) [Fact p.Prime]
local notation "F" => LocalKummer.RationalClosureTransport.h1Equiv e p
local notation "HΩ" => continuousCohomology 1 (LocalKummer.Rational.topRep (K := k) (Ω := Ω) p)
local notation "HΞ" => continuousCohomology 1 (LocalKummer.Rational.topRep (K := k) (Ω := Ξ) p)

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
  [CharZero k] [CompleteSpace k] [IsGalois k Ω] [IsGalois k Ξ] in
theorem kummerHom (a : kˣ) :
    F (LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p a).toAdd =
      (LocalKummer.Rational.kummerHom (K := k) (Ω := Ξ) p a).toAdd :=
  LocalKummer.RationalClosureTransport.h1Equiv_kummerClass e p
    (LocalKummer.rootTower p (Fact.out : p.Prime).pos (a : k)) a.ne_zero

omit [CharZero k] [CompleteSpace k] [IsGalois k Ω] [IsGalois k Ξ] in
theorem principalKummerHom (a : Additive (principalUnits (k := k))) :
    F (LocalPadicLog.principalKummerHom (k := k) (Ω := Ω) p a) =
      LocalPadicLog.principalKummerHom (k := k) (Ω := Ξ) p a := kummerHom e p a.toMul.1

omit [CharZero k] [CompleteSpace k] [IsGalois k Ω] [IsGalois k Ξ] in
theorem mem_principalImage_iff (x : HΩ) :
    F x ∈ principalKummerImage (k := k) (Ω := Ξ) p ↔ x ∈ principalKummerImage (k := k) (Ω := Ω) p := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, (F).injective ?_⟩
    exact (principalKummerHom e p a).trans ha
  · rintro ⟨a, rfl⟩
    exact ⟨a, (principalKummerHom e p a).symm⟩

def principalImageEquiv : principalKummerImage (k := k) (Ω := Ω) p ≃+ principalKummerImage (k := k) (Ω := Ξ) p where
  toFun x := ⟨F x.1, (mem_principalImage_iff e p x.1).mpr x.2⟩
  invFun y := ⟨(F).symm y.1, (mem_principalImage_iff e p ((F).symm y.1)).mp
    (by rw [(F).apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext ((F).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((F).apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add F x.1 y.1)

theorem principalImageLog_eq (hpk : ‖(p : k)‖ < 1)
    (x : principalKummerImage (k := k) (Ω := Ω) p) :
    principalImageLog (k := k) (Ω := Ξ) p hpk (principalImageEquiv e p x) =
      principalImageLog (k := k) (Ω := Ω) p hpk x := by
  obtain ⟨a, rfl⟩ := (LocalPadicLog.principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict_surjective x
  have he : principalImageEquiv e p
      ((LocalPadicLog.principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict a) =
      (LocalPadicLog.principalKummerHom (k := k) (Ω := Ξ) p).rangeRestrict a :=
    Subtype.ext (principalKummerHom e p a)
  rw [he, principalImageLog_class, principalImageLog_class]

omit [CharZero k] [CompleteSpace k] [IsGalois k Ω] [IsGalois k Ξ] in
theorem mem_saturatedImage_iff (x : HΩ) :
    F x ∈ saturatedKummerImage (k := k) (Ω := Ξ) p ↔ x ∈ saturatedKummerImage (k := k) (Ω := Ω) p := by
  change (∃ n : ℕ, (p ^ n) • F x ∈ principalKummerImage (k := k) (Ω := Ξ) p) ↔
    ∃ n : ℕ, (p ^ n) • x ∈ principalKummerImage (k := k) (Ω := Ω) p
  simp only [← map_nsmul F, mem_principalImage_iff e p]

def saturatedEquiv : saturatedKummerImage (k := k) (Ω := Ω) p ≃+ saturatedKummerImage (k := k) (Ω := Ξ) p where
  toFun x := ⟨F x.1, (mem_saturatedImage_iff e p x.1).mpr x.2⟩
  invFun y := ⟨(F).symm y.1, (mem_saturatedImage_iff e p ((F).symm y.1)).mp
    (by rw [(F).apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext ((F).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((F).apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add F x.1 y.1)

omit [CharZero k] [CompleteSpace k] [IsGalois k Ω] [IsGalois k Ξ] in
theorem saturatedEquiv_classOfImage (a : principalKummerImage (k := k) (Ω := Ω) p) (n : ℕ) :
    saturatedEquiv e p (saturatedClassOfImage p a n) =
      saturatedClassOfImage p (principalImageEquiv e p a) n :=
  Subtype.ext (map_smul F _ a.1)

theorem saturatedImageLog_eq (hpk : ‖(p : k)‖ < 1)
    (x : saturatedKummerImage (k := k) (Ω := Ω) p) :
    saturatedImageLog (k := k) (Ω := Ξ) p hpk (saturatedEquiv e p x) =
      saturatedImageLog (k := k) (Ω := Ω) p hpk x := by
  obtain ⟨n, hn⟩ := x.2
  rw [saturated_as_divided_image p x n hn, saturatedEquiv_classOfImage,
    saturatedImageLog_classOfImage, saturatedImageLog_classOfImage, principalImageLog_eq]

theorem saturatedExp_eq (hpk : ‖(p : k)‖ < 1) (y : k) :
    saturatedEquiv e p (saturatedExp (k := k) (Ω := Ω) p hpk y) =
      saturatedExp (k := k) (Ω := Ξ) p hpk y := by
  apply saturatedImageLog_injective p hpk
  rw [saturatedImageLog_eq, saturatedImageLog_saturatedExp, saturatedImageLog_saturatedExp]

omit [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
  [CharZero k] [CompleteSpace k] [IsGalois k Ω] [IsGalois k Ξ] in
theorem integralLift_iff (x : HΩ) :
    (∃ y : continuousCohomology 1 (LocalKummer.padicTateTopRep (K := k) (Ω := Ξ) p),
      LocalKummer.Rational.standardMap p y = F x) ↔
    ∃ y : continuousCohomology 1 (LocalKummer.padicTateTopRep (K := k) (Ω := Ω) p),
      LocalKummer.Rational.standardMap p y = x := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := (LocalKummer.ClosureTransport.h1Equiv e p).surjective y
    refine ⟨z, (F).injective ?_⟩
    rw [LocalKummer.RationalClosureTransport.h1Equiv_standardMap]
    exact hy
  · rintro ⟨y, rfl⟩
    exact ⟨LocalKummer.ClosureTransport.h1Equiv e p y,
      (LocalKummer.RationalClosureTransport.h1Equiv_standardMap e p y).symm⟩

variable (hpk : ‖(p : k)‖ < 1)
variable [Algebra ℚ_[p] k] [ContinuousSMul ℚ_[p] k]

def saturatedContinuousEquiv :
    saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk ≃L[ℚ_[p]]
      saturatedKummerPadicSubmodule (k := k) (Ω := Ξ) p hpk where
  toFun x := ⟨F x.1, (mem_saturatedImage_iff e p x.1).mpr x.2⟩
  invFun y := ⟨(F).symm y.1, (mem_saturatedImage_iff e p ((F).symm y.1)).mp
    (by rw [(F).apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext ((F).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((F).apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add F x.1 y.1)
  map_smul' r x := Subtype.ext (map_smul F r x.1)
  continuous_toFun := continuous_induced_rng.mpr ((F).continuous.comp continuous_subtype_val)
  continuous_invFun := continuous_induced_rng.mpr ((F).symm.continuous.comp continuous_subtype_val)

theorem saturatedPadicLog_eq (x : saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk) :
    saturatedPadicLog (Ω := Ξ) p hpk (saturatedContinuousEquiv e p hpk x) =
      saturatedPadicLog (Ω := Ω) p hpk x :=
  saturatedImageLog_eq e p hpk ⟨x.1, x.2⟩

end
end JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport
