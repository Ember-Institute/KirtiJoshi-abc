import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
source-id: JT-SCENE1-INTEGRAL-NORMALIZATION-LIFT
source: IUT I Definition 3.1(d), normalization of the covering square;
Mathlib integral extensions, integral-closure lifting and fraction fields.
fidelity: an injective integral cone map extends uniquely through the
normalization inside its fraction field when the target is normal and
integral over the same base. These are ordinary coordinate-ring statements.
Original proofs; no reference implementation copied.
boundary: no orbicurve or Cartesian producer law is assumed or supplied here.
-/

namespace JoshiTeich.Act1Scene1

universe u
noncomputable section

theorem injective_of_integral_of_base_injective
    {A T D : Type u} [CommRing A] [Nontrivial A] [CommRing T] [IsDomain T]
    [CommRing D] [Algebra A T] [Algebra A D] [Algebra.IsIntegral A T]
    (f : T →ₐ[A] D) (hD : Function.Injective (algebraMap A D)) : Function.Injective f := by
  apply (RingHom.injective_iff_ker_eq_bot f.toRingHom).mpr
  apply Ideal.IsIntegral.eq_bot_of_comap_eq_bot A
  ext a
  change f (algebraMap A T a) = 0 ↔ a = 0
  rw [f.commutes]
  exact ⟨fun h => hD (h.trans (map_zero _).symm), fun h => h ▸ map_zero _⟩

theorem integral_normalization_lift_exists
    {A T B N D : Type u} [CommRing A] [CommRing T] [IsDomain T]
    [CommRing B] [Field N] [CommRing D] [IsDomain D] [IsIntegrallyClosed D]
    [Algebra A T] [Algebra A B] [Algebra A N] [Algebra A D]
    [Algebra T B] [Algebra T N] [Algebra B N]
    [IsScalarTower A T N] [IsScalarTower A B N] [IsScalarTower T B N]
    [IsFractionRing T N] [Algebra.IsIntegral A B] [Algebra.IsIntegral A D]
    (hBN : Function.Injective (algebraMap B N)) (f : T →ₐ[A] D)
    (hf : Function.Injective f) :
    ∃ j : B →ₐ[A] D, Function.Injective j ∧
      j.toRingHom.comp (algebraMap T B) = f.toRingHom := by
  let L := FractionRing D
  letI : IsScalarTower A D L := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A L a = algebraMap D L (algebraMap A D a)
    rfl
  let g0 : T →ₐ[A] L := (IsScalarTower.toAlgHom A D L).comp f
  have hg0 : Function.Injective g0 := (IsFractionRing.injective D L).comp hf
  let g : N →ₐ[A] L := IsFractionRing.liftAlgHom (K := N) (g := g0) hg0
  let jN : B →ₐ[A] L := g.comp (IsScalarTower.toAlgHom A B N)
  letI : Algebra B L := jN.toRingHom.toAlgebra
  letI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun a => (jN.commutes a).symm
  let j : B →ₐ[A] D := IsIntegralClosure.lift A D L
  have hj (b : B) : algebraMap D L (j b) = g (algebraMap B N b) :=
    IsIntegralClosure.algebraMap_lift A D L b
  refine ⟨j, ?_, ?_⟩
  · intro b c h
    apply hBN
    apply g.injective
    calc
      g (algebraMap B N b) = algebraMap D L (j b) := (hj b).symm
      _ = algebraMap D L (j c) := congrArg (algebraMap D L) h
      _ = g (algebraMap B N c) := hj c
  · apply RingHom.ext
    intro t
    apply IsFractionRing.injective D L
    change algebraMap D L (j (algebraMap T B t)) = algebraMap D L (f t)
    rw [hj, ← IsScalarTower.algebraMap_apply T B N]
    exact IsFractionRing.lift_algebraMap hg0 t

theorem fraction_intermediate_ringHom_ext
    {T B N D : Type u} [CommRing T] [CommRing B] [Field N]
    [CommRing D] [IsDomain D] [Algebra T B] [Algebra T N] [Algebra B N]
    [IsScalarTower T B N] [IsFractionRing T N] [IsFractionRing B N]
    {j j' : B →+* D} (hj : Function.Injective j) (hj' : Function.Injective j')
    (hT : j.comp (algebraMap T B) = j'.comp (algebraMap T B)) : j = j' := by
  let L := FractionRing D
  let jL : B →+* L := (algebraMap D L).comp j
  let jL' : B →+* L := (algebraMap D L).comp j'
  have hjL : Function.Injective jL := (IsFractionRing.injective D L).comp hj
  have hjL' : Function.Injective jL' := (IsFractionRing.injective D L).comp hj'
  let e : N →+* L := IsFractionRing.lift hjL
  let e' : N →+* L := IsFractionRing.lift hjL'
  have he : e = e' := by
    apply IsFractionRing.ringHom_ext (A := T)
    intro t
    rw [IsScalarTower.algebraMap_apply T B N]
    change IsFractionRing.lift hjL (algebraMap B N (algebraMap T B t)) =
      IsFractionRing.lift hjL' (algebraMap B N (algebraMap T B t))
    rw [IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
    exact congrArg (algebraMap D L) (RingHom.congr_fun hT t)
  apply RingHom.ext
  intro b
  apply IsFractionRing.injective D L
  exact (IsFractionRing.lift_algebraMap hjL b).symm.trans
    ((RingHom.congr_fun he (algebraMap B N b)).trans (IsFractionRing.lift_algebraMap hjL' b))

end
end JoshiTeich.Act1Scene1
