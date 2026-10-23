import ArithmeticTeichmullerSpaces.Act1Scene1.AffineOrbicurvePresentationEquiv
import ArithmeticTeichmullerSpaces.Act1Scene1.AffineOrbicurvePresentationCategory
import Mathlib.RingTheory.Etale.Basic

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Mathlib etaleness of algebra equivalences;
the proved presentation cover category and ideal transport.
fidelity: multiplicity-preserving ring equivalences yield inverse presentation
covers. Their categorical isomorphisms recover the same coarse Spec isomorphism.
boundary: Scene1/Derived. This concerns the actual affine presentations;
no root-stack or arbitrary AG/TG realization is assumed.
-/

namespace JoshiTeich.Act1Scene1.AffineOrbicurvePresentation

open CategoryTheory
universe u
noncomputable section
variable {k : Type u} [Field k] {X Y : AffineOrbicurvePresentation k}

def Equiv.symm (e : Equiv X Y) : Equiv Y X where
  ringEquiv := e.ringEquiv.symm
  mult_eq q hq := by
    have : q.IsMaximal := hq
    have h := e.mult_eq (q.comap e.ringEquiv.symm) inferInstance
    have hq' : (q.comap e.ringEquiv.symm).comap e.ringEquiv = q :=
      Ideal.comap_of_equiv e.ringEquiv.toRingEquiv
    exact h.symm.trans (congrArg X.mult hq')

def Equiv.toCover (e : Equiv X Y) : Cover Y X where
  f := e.ringEquiv.toAlgHom
  injective := e.ringEquiv.injective
  isIntegral := e.ringEquiv.toRingHom.isIntegral_of_surjective e.ringEquiv.surjective
  ramification q hq := by
    have : q.IsMaximal := hq
    let : Algebra X.A Y.A := e.ringEquiv.toRingHom.toAlgebra
    let a : X.A ≃ₐ[X.A] Y.A :=
      { e.ringEquiv.toRingEquiv with commutes' := fun _ => rfl }
    have : Algebra.Etale X.A Y.A := Algebra.Etale.of_equiv a
    have he : q.ramificationIdx X.A = 1 := Ideal.ramificationIdx_eq_one q X.A
    exact (congrArg (fun n => n * Y.mult q) he).trans
      ((one_mul _).trans (e.mult_eq q hq).symm)

def Equiv.toIso (e : Equiv X Y) : Y ≅ X where
  hom := e.toCover
  inv := e.symm.toCover
  hom_inv_id := Cover.ext_f (AlgHom.ext fun a => e.ringEquiv.apply_symm_apply a)
  inv_hom_id := Cover.ext_f (AlgHom.ext fun a => e.ringEquiv.symm_apply_apply a)

theorem Equiv.toIso_coarse (e : Equiv X Y) :
    (coarseFunctor (k := k)).mapIso e.toIso = e.coarseIso := by
  apply Iso.ext
  rfl

end
end JoshiTeich.Act1Scene1.AffineOrbicurvePresentation
