import Mathlib.RingTheory.Perfectoid.Untilt
import Mathlib.RingTheory.Perfectoid.FontaineTheta

namespace JoshiTeich.Prologue.Perfectoid

open Ideal PreTilt WittVector

/-!
The perfectoid boundary is an adapter around mathlib's `PreTilt` and Fontaine
theta constructions.  The paper-level untilt and Frobenius picture is kept as
an explicit law rather than being smuggled into the theta-link contract.
-/

variable {O : Type*} [CommRing O] {p : ℕ}
  [Fact p.Prime] [Fact ¬ IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

noncomputable def untiltMap : PreTilt O p →* O :=
  PreTilt.untilt

noncomputable def thetaMap : WittVector p (PreTilt O p) →+* O :=
  WittVector.fontaineTheta O p

structure UntiltingLaws (u : PreTilt O p → O) : Prop where
  one : u 1 = 1
  reduction : ∀ x,
    Ideal.Quotient.mk (Ideal.span {(p : O)}) (u x) = PreTilt.coeff 0 x
  frobenius_scaling : ∀ (x : PreTilt O p) (n : ℕ),
    u (((frobeniusEquiv (PreTilt O p) p).symm^[n]) x) ^ p ^ n = u x

structure FontaineThetaLaws (u : PreTilt O p → O)
    (θ : WittVector p (PreTilt O p) → O) : Prop where
  teichmuller : ∀ x, θ (WittVector.teichmuller p x) = u x

theorem untiltMap_one : untiltMap (O := O) (p := p) 1 = 1 := by
  exact map_one _

theorem untiltMap_reduction (x : PreTilt O p) :
    Ideal.Quotient.mk (Ideal.span {(p : O)}) (untiltMap (O := O) (p := p) x) =
      PreTilt.coeff 0 x := by
  exact PreTilt.mk_untilt_eq_coeff_zero x

theorem untiltMap_frobenius_scaling (x : PreTilt O p) (n : ℕ) :
    untiltMap (O := O) (p := p) (((frobeniusEquiv (PreTilt O p) p).symm^[n]) x) ^ p ^ n =
      untiltMap (O := O) (p := p) x := by
  exact PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n

theorem canonicalUntiltingLaws :
    UntiltingLaws (untiltMap (O := O) (p := p)) := by
  constructor
  · exact untiltMap_one
  · exact untiltMap_reduction
  · exact untiltMap_frobenius_scaling

theorem thetaMap_teichmuller (x : PreTilt O p) :
    thetaMap (O := O) (p := p) (WittVector.teichmuller p x) = untiltMap (O := O) (p := p) x := by
  exact WittVector.fontaineTheta_teichmuller x

theorem canonicalFontaineThetaLaws :
    FontaineThetaLaws (untiltMap (O := O) (p := p)) (thetaMap (O := O) (p := p)) := by
  exact ⟨thetaMap_teichmuller⟩

end JoshiTeich.Prologue.Perfectoid
