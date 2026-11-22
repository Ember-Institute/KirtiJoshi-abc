import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerImageLogarithm
import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Recognition

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v
noncomputable section

variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]
local notation "G" => Ω ≃ₐ[K] Ω
local notation "X" => Rational.topRep (K := K) (Ω := Ω) p

/-- A coboundary for the mapped cocycle of the chosen root tower kills the
corresponding rational Kummer class after the same change of coefficients. -/
theorem map_kummerHom_eq_zero_of_rootTower_coboundary (Y : TopRep.{v} ℚ_[p] G) (coefficient : X →L[ℚ_[p]] Y)
    (hCoefficient : ∀ g x, coefficient ((X).ρ g x) = Y.ρ g (coefficient x))
    (a : Kˣ) (witness : Y)
    (hWitness : ∀ g : G, coefficient (Rational.cocycle p
      ((rootTower (Ω := Ω) p (Fact.out : p.Prime).pos (a : K)).continuousCocycleValue
        (Fact.out : p.Prime).pos a.ne_zero) g) = Y.ρ g witness - witness) :
    ContinuousH1Semilinear.map X Y coefficient hCoefficient
      (Rational.kummerHom (Ω := Ω) p a).toAdd = 0 := by
  change ContinuousH1Semilinear.map X Y coefficient hCoefficient
    (Rational.classOfCocycle p
      ((rootTower (Ω := Ω) p (Fact.out : p.Prime).pos (a : K)).continuousCocycleValue
        (Fact.out : p.Prime).pos a.ne_zero)) = 0
  rw [Rational.classOfCocycle, ContinuousH1Semilinear.map_classOf]
  refine (ContinuousH1Recognition.classOf_eq_zero_iff _ _ _).mpr ⟨witness, ?_⟩
  intro g
  exact hWitness g

end
end JoshiTeich.Act1Scene1.LocalKummer
