import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerMultiplicativity
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicRationalKummerNonvanishing

/-!
source-id: JT-SCENE1-PRINCIPAL-KUMMER-IMAGE-LOGARITHM
source: principal-unit Kummer construction and ordinary logarithm in Joshi III
(3190--3236), with standard continuous rational H1.
fidelity: constructs an additive ordinary logarithm on the actual image of
principal units in rational Kummer cohomology. Rationally trivial principal
units have zero log, so the value is independent of the representing unit.
This image is not identified with H^1_e, and the map is not asserted to be the
Bloch--Kato logarithm, continuous, injective or surjective.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open scoped Valued Topology
universe u v
noncomputable section

namespace LocalKummer.Rational
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]

private theorem classOfCocycle_mul (f g : continuousCocycles (K := K) (Ω := Ω) p) :
    classOfCocycle p (multiplyCocycles f g) = classOfCocycle p f + classOfCocycle p g := by
  have hc : cocycle p (multiplyCocycles f g) = cocycle p f + cocycle p g := by
    ext σ
    apply ULift.ext
    exact map_add (coefficientMap p) _ _
  unfold classOfCocycle
  calc
    _ = ContinuousH1Homogeneous.classOf (topRep p) (cocycle p f + cocycle p g)
        (ContinuousH1Homogeneous.cocycle_add_law _ _ _ (cocycle_law p f) (cocycle_law p g)) := by
      congr 1
    _ = _ := ContinuousH1Homogeneous.classOf_add _ _ _ (cocycle_law p f) (cocycle_law p g)

def kummerHom : Kˣ →* Multiplicative (continuousCohomology 1
    (topRep (K := K) (Ω := Ω) p)) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd
    (toH1 p ((rootTower (Ω := Ω) p (Fact.out : p.Prime).pos (a : K)).kummerClass
      (Fact.out : p.Prime).pos a.ne_zero))) (by
    intro a b
    let R := rootTower (Ω := Ω) p (Fact.out : p.Prime).pos (a : K)
    let S := rootTower (Ω := Ω) p (Fact.out : p.Prime).pos (b : K)
    have he := (rootTower (Ω := Ω) p (Fact.out : p.Prime).pos ((a * b : Kˣ) : K)).kummerClass_eq
      (R.mul S) (Fact.out : p.Prime).pos (a * b).ne_zero
    change toH1 p ((rootTower (Ω := Ω) p (Fact.out : p.Prime).pos
      ((a * b : Kˣ) : K)).kummerClass (Fact.out : p.Prime).pos (a * b).ne_zero) = _
    rw [he]
    have hc : (R.mul S).continuousCocycleValue (Fact.out : p.Prime).pos (a * b).ne_zero =
        multiplyCocycles (R.continuousCocycleValue (Fact.out : p.Prime).pos a.ne_zero)
          (S.continuousCocycleValue (Fact.out : p.Prime).pos b.ne_zero) := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro σ
      exact R.kummerCocycle_mul S (Fact.out : p.Prime).pos a.ne_zero b.ne_zero σ
    change classOfCocycle p ((R.mul S).continuousCocycleValue _ _) = _
    rw [hc, classOfCocycle_mul]
    rfl)

end LocalKummer.Rational

namespace LocalPadicLog
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]

/-- Principal units of the actual valued base field. -/
def principalUnits : Subgroup kˣ where
  carrier := {a | ‖(a : k) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' := fun ha hb => norm_mul_sub_one_lt ha hb
  inv_mem' := by
    intro a ha
    change ‖((a⁻¹ : kˣ) : k) - 1‖ < 1
    rw [Units.val_inv_eq_inv_val]
    exact norm_inv_sub_one_lt ha

variable [CharZero k] [CompleteSpace k]
variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime]

def principalKummerHom : Additive (principalUnits (k := k)) →+
    continuousCohomology 1 (LocalKummer.Rational.topRep (K := k) (Ω := Ω) p) where
  toFun a := (LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p a.toMul.1).toAdd
  map_zero' := by
    change (LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p 1).toAdd = 0
    rw [map_one]
    rfl
  map_add' a b := congrArg Multiplicative.toAdd
    (map_mul (LocalKummer.Rational.kummerHom (K := k) (Ω := Ω) p) a.toMul.1 b.toMul.1)

def principalLogHom (hpk : ‖(p : k)‖ < 1) : Additive (principalUnits (k := k)) →+ k where
  toFun a := padicLog (a.toMul.1 : k)
  map_zero' := padicLog_one
  map_add' a b := padicLog_mul (Fact.out : p.Prime) hpk a.toMul.2 b.toMul.2

theorem principalLog_eq_zero_of_kummer_eq_zero (hpk : ‖(p : k)‖ < 1)
    (a : Additive (principalUnits (k := k)))
    (ha : principalKummerHom (Ω := Ω) p a = 0) : principalLogHom p hpk a = 0 := by
  by_contra hlog
  exact rationalKummer_ne_zero_of_log_ne_zero
    (LocalKummer.rootTower (Ω := Ω) p (Fact.out : p.Prime).pos (a.toMul.1 : k))
    hpk a.toMul.2 hlog ha

theorem principalLog_eq_of_kummer_eq (hpk : ‖(p : k)‖ < 1)
    (a b : Additive (principalUnits (k := k)))
    (hab : principalKummerHom (Ω := Ω) p a = principalKummerHom p b) :
    principalLogHom p hpk a = principalLogHom p hpk b := by
  have hzero : principalKummerHom (Ω := Ω) p (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have h := principalLog_eq_zero_of_kummer_eq_zero p hpk (a - b) hzero
  rw [map_sub] at h
  exact sub_eq_zero.mp h

/-- The actual image subgroup in standard rational continuous cohomology. -/
def principalKummerImage := (principalKummerHom (k := k) (Ω := Ω) p).range

private theorem image_kernel_le_log_kernel (hpk : ‖(p : k)‖ < 1) :
    (principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict.ker ≤
      (principalLogHom (k := k) p hpk).ker := by
  intro a ha
  apply principalLog_eq_zero_of_kummer_eq_zero (Ω := Ω) p hpk a
  exact congrArg Subtype.val (show (principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict a = 0 from ha)

def principalImageLog (hpk : ‖(p : k)‖ < 1) :
    principalKummerImage (k := k) (Ω := Ω) p →+ k :=
  ((principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict.liftOfSurjective
    (principalKummerHom (k := k) (Ω := Ω) p).rangeRestrict_surjective)
      ⟨principalLogHom p hpk, image_kernel_le_log_kernel p hpk⟩

theorem principalImageLog_class (hpk : ‖(p : k)‖ < 1)
    (a : Additive (principalUnits (k := k))) :
    principalImageLog (Ω := Ω) p hpk ((principalKummerHom p).rangeRestrict a) =
      padicLog (a.toMul.1 : k) := by
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a

theorem principalImageLog_nsmul (hpk : ‖(p : k)‖ < 1)
    (x : principalKummerImage (k := k) (Ω := Ω) p) (n : ℕ) :
    principalImageLog (Ω := Ω) p hpk (n • x) =
      n • principalImageLog (Ω := Ω) p hpk x :=
  map_nsmul (principalImageLog (Ω := Ω) p hpk) n x

end LocalPadicLog
end
end JoshiTeich.Act1Scene1
