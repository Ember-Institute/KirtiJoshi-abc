import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Scalar
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerPadicPowerTower
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerCoefficientChange

/-!
source-id: JT-SCENE1-KUMMER-PADIC-POWER-CLASS
source: actual p-adic power root tower and coefficient-linear standard H1;
Joshi III 3190--3226.
fidelity: descends the actual tower cocycle identity to integral and rational
standard H1 scalar identities. Root-choice independence identifies the chosen
principal-unit Kummer homomorphism, whose image is closed under the ambient
Z_p action. H1e/BK and topological comparison remain separate obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.PadicPowerTower
open scoped Valued Topology
universe u v
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k]
variable {Ω : Type v} [Field Ω] [Algebra k Ω] [Algebra.IsIntegral k Ω]
variable (hpk : ‖(p : k)‖ < 1) (a : LocalPadicLog.principalUnits (k := k)) (r : ℤ_[p])
variable (R : RootTower (Ω := Ω) p (a.1 : k))

theorem tower_padicAdditiveCocycle :
    padicAdditiveCocycle p ((tower hpk a r R).continuousCocycleValue
      (Fact.out : p.Prime).pos (LocalPadicLog.principalPadicPower hpk a r).1.ne_zero) =
    r • padicAdditiveCocycle p (R.continuousCocycleValue (Fact.out : p.Prime).pos a.1.ne_zero) := by
  ext σ
  exact congrArg Additive.ofMul (tower_cocycle hpk a r R σ)

theorem tower_padicClass :
    padicClassOfCocycle p ((tower hpk a r R).continuousCocycleValue
      (Fact.out : p.Prime).pos (LocalPadicLog.principalPadicPower hpk a r).1.ne_zero) =
    r • padicClassOfCocycle p (R.continuousCocycleValue (Fact.out : p.Prime).pos a.1.ne_zero) := by
  unfold padicClassOfCocycle
  have he := tower_padicAdditiveCocycle hpk a r R
  calc
    _ = ContinuousH1Homogeneous.classOf (padicTateTopRep p)
        (r • padicAdditiveCocycle p (R.continuousCocycleValue _ _))
        (ContinuousH1Homogeneous.cocycle_smul_law _ _ _ (padicAdditiveCocycle_law p _)) := by
      congr 1
    _ = _ := ContinuousH1Homogeneous.classOf_smul _ _ _ _

variable [CharZero Ω] [IsAlgClosed Ω]

theorem tower_rationalClass :
    Rational.classOfCocycle p ((tower hpk a r R).continuousCocycleValue
      (Fact.out : p.Prime).pos (LocalPadicLog.principalPadicPower hpk a r).1.ne_zero) =
    (r : ℚ_[p]) • Rational.classOfCocycle p
      (R.continuousCocycleValue (Fact.out : p.Prime).pos a.1.ne_zero) := by
  have he := congrArg (Rational.standardMap (K := k) (Ω := Ω) p)
    (tower_padicClass hpk a r R)
  simpa only [map_smulₛₗ, Rational.standardMap_classOfCocycle,
    show PadicInt.Coe.ringHom r = (r : ℚ_[p]) from rfl] using he

end
end JoshiTeich.Act1Scene1.LocalKummer.PadicPowerTower

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k]
variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime]
variable (hpk : ‖(p : k)‖ < 1)

theorem principalKummerHom_principalPadicPower (a : principalUnits (k := k)) (r : ℤ_[p]) :
    principalKummerHom (Ω := Ω) p (Additive.ofMul (principalPadicPower hpk a r)) =
      (r : ℚ_[p]) • principalKummerHom (Ω := Ω) p (Additive.ofMul a) := by
  let R := LocalKummer.rootTower (Ω := Ω) p (Fact.out : p.Prime).pos (a.1 : k)
  let S := LocalKummer.rootTower (Ω := Ω) p (Fact.out : p.Prime).pos
    ((principalPadicPower hpk a r).1 : k)
  have hchoice := S.kummerClass_eq (LocalKummer.PadicPowerTower.tower hpk a r R)
    (Fact.out : p.Prime).pos (principalPadicPower hpk a r).1.ne_zero
  have he := congrArg (LocalKummer.Rational.toH1 (K := k) (Ω := Ω) p) hchoice
  exact he.trans (LocalKummer.PadicPowerTower.tower_rationalClass hpk a r R)

include hpk in
/-- The scalar action is the existing one on standard rational H1. -/
theorem padicInt_smul_mem_principalKummerImage (r : ℤ_[p])
    {x : continuousCohomology 1 (LocalKummer.Rational.topRep (K := k) (Ω := Ω) p)}
    (hx : x ∈ principalKummerImage p) : (r : ℚ_[p]) • x ∈ principalKummerImage p := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨Additive.ofMul (principalPadicPower hpk a.toMul r),
    principalKummerHom_principalPadicPower p hpk a.toMul r⟩

end
end JoshiTeich.Act1Scene1.LocalPadicLog
