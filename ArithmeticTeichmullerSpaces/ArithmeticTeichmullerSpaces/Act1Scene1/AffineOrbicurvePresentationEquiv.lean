import ArithmeticTeichmullerSpaces.Act1Scene1.AffineOrbicurvePresentation
import Mathlib.Algebra.Field.Equiv

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Mathlib ideal transport and affine Spec.
fidelity: a coefficient-algebra equivalence transports the closed-point
multiplicities and their finite support to another actual coordinate ring.
Presentation equivalences induce the corresponding coarse-scheme isomorphisms.
boundary: Scene1/Derived. These are affine presentations, without a root-stack
or arbitrary AG.Orbicurve realization.
-/

namespace JoshiTeich.Act1Scene1.AffineOrbicurvePresentation

open AlgebraicGeometry
universe u
noncomputable section
variable {k : Type u} [Field k]

structure Equiv (X Y : AffineOrbicurvePresentation k) where
  ringEquiv : X.A ≃ₐ[k] Y.A
  mult_eq : ∀ q : Ideal Y.A, q.IsMaximal → X.mult (q.comap ringEquiv) = Y.mult q

def Equiv.coarseIso {X Y : AffineOrbicurvePresentation k} (e : Equiv X Y) :
    Y.coarseScheme ≅ X.coarseScheme :=
  Scheme.Spec.mapIso e.ringEquiv.toRingEquiv.toCommRingCatIso.op

variable (X : AffineOrbicurvePresentation k) (A : Type u)
  [CommRing A] [IsDomain A] [Algebra k A] [IsDedekindDomain A] [Algebra.FiniteType k A]
  (e : A ≃ₐ[k] X.A)

def ofAlgEquiv : AffineOrbicurvePresentation k where
  A := A
  not_isField h := X.not_isField (MulEquiv.isField h e.symm.toRingEquiv.toMulEquiv)
  mult p := X.mult (p.map e)
  mult_pos p hp := X.mult_pos (p.map e)
    ((Ideal.isMaximal_map_iff_of_bijective e e.bijective).mpr hp)
  finite_mult := by
    refine (X.finite_mult.image (fun q => q.comap e)).subset ?_
    intro p hp
    exact ⟨p.map e,
      ⟨(Ideal.isMaximal_map_iff_of_bijective e e.bijective).mpr hp.1, hp.2⟩,
      Ideal.comap_map_of_bijective e e.bijective⟩

def ofAlgEquivEquiv : Equiv (ofAlgEquiv X A e) X where
  ringEquiv := e
  mult_eq q _ := congrArg X.mult (Ideal.map_comap_of_surjective e e.surjective q)

end
end JoshiTeich.Act1Scene1.AffineOrbicurvePresentation
