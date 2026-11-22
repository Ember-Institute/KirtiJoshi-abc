import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Recognition
import Solutions.Source_ReferenceIutCor312KummerPreTiltGalois

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

/-- The rational Kummer class vanishes after change of coefficients exactly
when the mapped cocycle of the given tower is a coboundary. -/
theorem map_kummerHom_eq_zero_iff_rootTower_coboundary
    (Y : TopRep.{v} ℚ_[p] G) (coefficient : X →L[ℚ_[p]] Y)
    (hCoefficient : ∀ g x, coefficient ((X).ρ g x) = Y.ρ g (coefficient x))
    (a : Kˣ) (R : RootTower (Ω := Ω) p (a : K)) :
    ContinuousH1Semilinear.map X Y coefficient hCoefficient
      (Rational.kummerHom (Ω := Ω) p a).toAdd = 0 ↔
      ∃ witness : Y, ∀ g : G, coefficient (Rational.cocycle p
        (R.continuousCocycleValue (Fact.out : p.Prime).pos a.ne_zero) g) =
          Y.ρ g witness - witness := by
  let towerCocycle := R.continuousCocycleValue (Fact.out : p.Prime).pos a.ne_zero
  let sourceCocycle : C(G, X) := Rational.cocycle p towerCocycle
  let targetCocycle : C(G, Y) := ContinuousH1Semilinear.post coefficient sourceCocycle
  have hSource : ∀ g h, sourceCocycle (g * h) = (X).ρ g (sourceCocycle h) + sourceCocycle g :=
    Rational.cocycle_law p towerCocycle
  have hTarget : ∀ g h, targetCocycle (g * h) = Y.ρ g (targetCocycle h) + targetCocycle g := by
    intro g h
    change coefficient (sourceCocycle (g * h)) =
      Y.ρ g (coefficient (sourceCocycle h)) + coefficient (sourceCocycle g)
    rw [hSource g h, map_add, hCoefficient g]
  have hClass : (Rational.kummerHom (Ω := Ω) p a).toAdd =
      ContinuousH1Homogeneous.classOf X sourceCocycle hSource :=
    Rational.kummerHom_toAdd_eq_classOfRootTower p a R
  have hMap := ContinuousH1Semilinear.map_classOf X Y coefficient hCoefficient sourceCocycle hSource
  change ContinuousH1Semilinear.map X Y coefficient hCoefficient
    (ContinuousH1Homogeneous.classOf X sourceCocycle hSource) =
      ContinuousH1Homogeneous.classOf Y targetCocycle hTarget at hMap
  change ContinuousH1Semilinear.map X Y coefficient hCoefficient
    (Rational.kummerHom (Ω := Ω) p a).toAdd = 0 ↔ ∃ witness : Y, ∀ g : G,
      targetCocycle g = Y.ρ g witness - witness
  rw [hClass, hMap]
  exact ContinuousH1Recognition.classOf_eq_zero_iff Y targetCocycle hTarget

end

end JoshiTeich.Act1Scene1.LocalKummer
