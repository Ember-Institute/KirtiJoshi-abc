/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/U2/Assembly.lean (`Hom.descend`)
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.AffineOrbicurvePresentationCategory
import Mathlib.RingTheory.Ideal.GoingUp

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.AffineOrbicurvePresentation

universe u

variable {k : Type u} [Field k]

/-- A factored cover descends through the given cover `ψ`. -/
def Cover.descend {Z Y C : AffineOrbicurvePresentation k} (ψ : Cover Z Y) (χ : Cover Z C)
    (g : C.A →ₐ[k] Y.A) (hg : ψ.f.comp g = χ.f) : Cover Y C where
  f := g
  injective := by
    intro a b hab
    apply χ.injective
    rw [← hg]
    exact congrArg ψ.f hab
  isIntegral := by
    have hcomp : ψ.f.toRingHom.comp g.toRingHom = χ.f.toRingHom :=
      congrArg AlgHom.toRingHom hg
    apply RingHom.IsIntegral.tower_bot g.toRingHom ψ.f.toRingHom ψ.injective
    rw [hcomp]
    exact χ.isIntegral
  ramification w hw := by
    have : w.IsMaximal := hw
    letI : Algebra Y.A Z.A := ψ.f.toRingHom.toAlgebra
    have : Algebra.IsIntegral Y.A Z.A := ⟨ψ.isIntegral⟩
    obtain ⟨q, hq, hqw⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := Z.A) w (by
      intro a ha
      have ha' : ψ.f a = 0 := ha
      rw [show a = 0 from ψ.injective (ha'.trans (map_zero ψ.f).symm)]
      exact w.zero_mem)
    change q.comap ψ.f.toRingHom = w at hqw
    have hcomp : ψ.f.toRingHom.comp g.toRingHom = χ.f.toRingHom :=
      congrArg AlgHom.toRingHom hg
    have htower :=
      FunctionFieldNormalization.ramificationIdx_comp g.toRingHom ψ.f.toRingHom ψ.injective q
    have hidx := (congrArg (fun f : C.A →+* Z.A =>
      letI := f.toAlgebra
      q.ramificationIdx C.A) hcomp).symm.trans htower
    have hcontract : q.comap χ.f.toRingHom = w.comap g.toRingHom := by
      rw [← hcomp, ← Ideal.comap_comap, hqw]
    have hχ := χ.ramification q hq
    have hψ := ψ.ramification q hq
    change (letI := χ.f.toRingHom.toAlgebra; q.ramificationIdx C.A) * Z.mult q =
      C.mult (q.comap χ.f.toRingHom) at hχ
    change (letI := ψ.f.toRingHom.toAlgebra; q.ramificationIdx Y.A) * Z.mult q =
      Y.mult (q.comap ψ.f.toRingHom) at hψ
    rw [hidx, Nat.mul_assoc, hψ, hqw, hcontract] at hχ
    exact hχ

end JoshiTeich.Act1Scene1.AffineOrbicurvePresentation
