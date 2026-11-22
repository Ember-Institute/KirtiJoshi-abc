import Solutions.Source_ReferenceIutCor312PreTiltGalois
import Solutions.Source_ReferenceIutCor312RootTowerPreTilt
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerImageLogarithm

/-!
Joshi III §9.6, compatible roots of the principal unit and its Kummer class.
The Galois ratio in each algebraic coordinate gives the factor in the
valuation integers, in their quotient by p and in the pretilt.
-/

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.LocalKummer

universe u v w

noncomputable section

namespace Rational

/-- The rational Kummer class of a unit is represented by the cocycle of any
fixed compatible root tower for the unit. -/
theorem kummerHom_toAdd_eq_classOfRootTower
    {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
    [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime] (a : Kˣ) (R : RootTower (Ω := Ω) p (a : K)) :
    (kummerHom (Ω := Ω) p a).toAdd =
      classOfCocycle p (R.continuousCocycleValue (Fact.out : p.Prime).pos a.ne_zero) := by
  let S := rootTower (Ω := Ω) p (Fact.out : p.Prime).pos (a : K)
  change toH1 p (S.kummerClass (Fact.out : p.Prime).pos a.ne_zero) = _
  exact (congrArg (toH1 (K := K) (Ω := Ω) p)
    (S.kummerClass_eq R (Fact.out : p.Prime).pos a.ne_zero)).trans (toH1_class p _)

end Rational

namespace RootTower

section Map

variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable {C : Type w} [Field C] {p : ℕ} [Fact p.Prime] {a : K}
variable (R : RootTower (Ω := Ω) p a) (j : Ω →+* C) (hne : a ≠ 0)
variable (σ : Ω ≃ₐ[K] Ω)

/-- Map the original Kummer coordinates into the field used for the pretilt. -/
def mapKummerCocycle : cyclotomicTateGroup p C := by
  let value := R.kummerCocycle (Fact.out : p.Prime).pos hne σ
  let mapUnits : Ωˣ →* Cˣ := Units.map j.toMonoidHom
  refine ⟨fun n => mapUnits (value.1 n), ?_⟩
  constructor
  · intro n
    change mapUnits (value.1 n) ^ (p ^ n) = 1
    rw [← map_pow, value.2.1 n, map_one]
  · intro n
    change mapUnits (value.1 (n + 1)) ^ p = mapUnits (value.1 n)
    rw [← map_pow, value.2.2 n]

theorem mapKummerCocycle_apply (n : ℕ) :
    ((R.mapKummerCocycle j hne σ).1 n : C) = j (σ (R.root n)) / j (R.root n) := by
  change j ((R.kummerCocycle (Fact.out : p.Prime).pos hne σ).1 n : Ω) = _
  rw [R.kummerCocycle_apply, RootTower.ratio, map_div₀]

end Map

section Completion

open JoshiTeich.Prologue

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] {a : K}

local notation "Ω₀" => CompletedAlgebraicClosure.Algebraic K
local notation "C" => CompletedAlgebraicClosure.Field K
local notation "ι" => (UniformSpace.Completion.coeRingHom : Ω₀ →+* C)
local notation "𝒪" => LocalGeometricFontaine.integerRing C
local notation "q" => Ideal.Quotient.mk (Ideal.span {(p : 𝒪)})

variable (R : RootTower (Ω := CompletedAlgebraicClosure.Algebraic K) p a)
variable (ha : ‖(algebraMap K (CompletedAlgebraicClosure.Field K) a)‖ ≤ 1)
variable (hne : a ≠ 0)
variable (σ : CompletedAlgebraicClosure.Algebraic K ≃ₐ[K] CompletedAlgebraicClosure.Algebraic K)

/-- At each level the Galois image is the Kummer factor times the original
root, viewed in the valuation integers of the same completed field. -/
theorem extendGaloisIntegers_integralCoordinate (n : ℕ) :
    CompletedAlgebraicClosure.extendGaloisIntegers σ (R.integralCoordinate ι ha n) =
      CyclotomicTateTilt.coordinate C p (R.mapKummerCocycle ι hne σ) n *
        R.integralCoordinate ι ha n := by
  apply Subtype.ext
  change (CompletedAlgebraicClosure.extendGaloisIntegers σ (R.integralCoordinate ι ha n) : C) =
    ((R.mapKummerCocycle ι hne σ).1 n : C) * ι (R.root n)
  rw [CompletedAlgebraicClosure.extendGaloisIntegers_coe, R.mapKummerCocycle_apply]
  change CompletedAlgebraicClosure.extendGalois σ (R.root n : C) =
    (σ (R.root n) : C) / (R.root n : C) * (R.root n : C)
  rw [CompletedAlgebraicClosure.extendGalois_coe]
  exact (div_mul_cancel₀ _ ((map_ne_zero ι).mpr
    (R.root_ne_zero (Fact.out : p.Prime).pos hne n))).symm

theorem extendGaloisModP_integralCoordinate (n : ℕ) :
    CompletedAlgebraicClosure.extendGaloisModP p σ (q (R.integralCoordinate ι ha n)) =
      q (CyclotomicTateTilt.coordinate C p (R.mapKummerCocycle ι hne σ) n) *
        q (R.integralCoordinate ι ha n) := by
  rw [CompletedAlgebraicClosure.extendGaloisModP_mk,
    R.extendGaloisIntegers_integralCoordinate ha hne σ n, map_mul]

variable [Fact (0 < ‖(p : CompletedAlgebraicClosure.Field K)‖ ∧
  ‖(p : CompletedAlgebraicClosure.Field K)‖ < 1)]

/-- The pretilt action multiplies the root tower by the reduction of its
Kummer cocycle in the same pretilt ring. -/
theorem extendGaloisPreTilt_toGeometricPreTilt :
    CompletedAlgebraicClosure.extendGaloisPreTilt p σ (R.toGeometricPreTilt ι ha) =
      CyclotomicTateTilt.toPreTilt C p (R.mapKummerCocycle ι hne σ) *
        R.toGeometricPreTilt ι ha := by
  apply Perfection.ext
  intro n
  rw [CompletedAlgebraicClosure.coeff_extendGaloisPreTilt]
  exact R.extendGaloisModP_integralCoordinate ha hne σ n

end Completion

end RootTower

end

end JoshiTeich.Act1Scene1.LocalKummer
