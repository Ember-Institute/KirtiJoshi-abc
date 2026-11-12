import ArithmeticTeichmullerSpaces.Act1Scene1.AffineOrbicurvePresentation
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationInertia
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); the proved ramification tower formula;
Mathlib's finite integral algebras and affine Spec functor.
fidelity: presentation covers form a category. Composition preserves their
closed-point ramification law. Every coarse map is finite, and coarse Spec
is a functor on the actual coordinate maps.
boundary: Scene1/Derived. No cartesian, root-stack or arbitrary AG/TG law
is assumed or supplied by this category construction.
-/

namespace JoshiTeich.Act1Scene1.AffineOrbicurvePresentation

open CategoryTheory AlgebraicGeometry
universe u
noncomputable section
variable {k : Type u} [Field k]

@[ext] theorem Cover.ext_f {X Y : AffineOrbicurvePresentation k}
    {f g : Cover X Y} (h : f.f = g.f) : f = g := by
  cases f
  cases g
  cases h
  rfl

def Cover.id (X : AffineOrbicurvePresentation k) : Cover X X where
  f := AlgHom.id k X.A
  injective := Function.injective_id
  isIntegral := (RingHom.id X.A).isIntegral_of_surjective Function.surjective_id
  ramification q hq := by
    have : q.IsMaximal := hq
    let := (RingHom.id X.A).toAlgebra
    have he : q.ramificationIdx X.A = 1 := Ideal.ramificationIdx_eq_one q X.A
    change q.ramificationIdx X.A * X.mult q = X.mult (q.comap (RingHom.id X.A))
    rw [he, one_mul, Ideal.comap_id]

def Cover.comp {X Y Z : AffineOrbicurvePresentation k} (f : Cover X Y) (g : Cover Y Z) :
    Cover X Z where
  f := f.f.comp g.f
  injective := f.injective.comp g.injective
  isIntegral := RingHom.IsIntegral.trans g.f.toRingHom f.f.toRingHom g.isIntegral f.isIntegral
  ramification q hq := by
    have : q.IsMaximal := hq
    have hw : (q.comap f.f).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f.f.toRingHom f.isIntegral q
    have he := FunctionFieldNormalization.ramificationIdx_comp
      g.f.toRingHom f.f.toRingHom f.injective q
    let e : ℕ := letI := g.f.toRingHom.toAlgebra; (q.comap f.f).ramificationIdx Z.A
    exact (congrArg (fun n => n * X.mult q) he).trans
      ((Nat.mul_assoc _ _ _).trans
        ((congrArg (fun n => e * n) (f.ramification q hq)).trans
          (g.ramification _ hw)))

instance category : Category.{u} (AffineOrbicurvePresentation k) where
  Hom := Cover
  id := Cover.id
  comp := Cover.comp
  id_comp _ := Cover.ext_f rfl
  comp_id _ := Cover.ext_f rfl
  assoc _ _ _ := Cover.ext_f rfl

def coarseFunctor : AffineOrbicurvePresentation k ⥤ Scheme.{u} where
  obj := coarseScheme
  map f := f.coarseMap
  map_id X := Spec.map_id (CommRingCat.of X.A)
  map_comp f g := Spec.map_comp (CommRingCat.ofHom g.f.toRingHom) (CommRingCat.ofHom f.f.toRingHom)

theorem Cover.comp_coarseMap {X Y Z : AffineOrbicurvePresentation k}
    (f : Cover X Y) (g : Cover Y Z) :
    (Cover.comp f g).coarseMap = f.coarseMap ≫ g.coarseMap :=
  (coarseFunctor (k := k)).map_comp (X := X) (Y := Y) (Z := Z) f g

theorem Cover.finite {X Y : AffineOrbicurvePresentation k} (f : Cover X Y) :
    f.f.toRingHom.Finite := by
  let := f.f.toRingHom.toAlgebra
  have : IsScalarTower k Y.A X.A := IsScalarTower.of_algebraMap_eq fun a => (f.f.commutes a).symm
  have : Algebra.FiniteType Y.A X.A := Algebra.FiniteType.of_restrictScalars_finiteType k Y.A X.A
  have : Algebra.IsIntegral Y.A X.A := ⟨f.isIntegral⟩
  exact Algebra.IsIntegral.finite

instance finite_coarseMap {X Y : AffineOrbicurvePresentation k} (f : Cover X Y) :
    IsFinite f.coarseMap :=
  (IsFinite.SpecMap_iff _).mpr f.finite

end
end JoshiTeich.Act1Scene1.AffineOrbicurvePresentation
