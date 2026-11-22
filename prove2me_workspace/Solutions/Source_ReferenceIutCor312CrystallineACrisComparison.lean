import Solutions.Source_ReferenceIutCor312AdicRingEquiv
import Solutions.Source_ReferenceIutCor312CrystallineA0Comparison
import Solutions.Source_ReferenceIutCor312CrystallineLog

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

noncomputable section

variable {C C' : Type*} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable [NormedField C'] [IsUltrametricDist C'] [CompleteSpace C']
variable (p : ℕ) [Fact p.Prime]
variable [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable [Fact (0 < ‖(p : C')‖ ∧ ‖(p : C')‖ < 1)]
variable (e : C ≃+* C') (d : ℕ) (hd : 0 < d) (hnorm : ∀ x : C, ‖e x‖ ^ d = ‖x‖)

local notation "I" => (Ideal.span {(p : A0 C p)} : Ideal (A0 C p))
local notation "I'" => (Ideal.span {(p : A0 C' p)} : Ideal (A0 C' p))

private theorem equivA0_map_span_prime : I' = (I).map (equivA0 p e d hd hnorm).toRingHom := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/-- The equivalence of the divided-power subalgebras extends to their
p-adic completions. -/
def equivACris : ACris C p ≃+* ACris C' p :=
  AdicCompletion.ringEquivOfRingEquiv I I' (equivA0 p e d hd hnorm)
    (equivA0_map_span_prime p e d hd hnorm)

theorem eval_equivACris_of_eq (k : ℕ) (z : ACris C p) (x : A0 C p)
    (hx : AdicCompletion.evalₐ I k z = Ideal.Quotient.mk (I ^ k) x) :
    AdicCompletion.evalₐ I' k (equivACris p e d hd hnorm z) =
      Ideal.Quotient.mk (I' ^ k) (equivA0 p e d hd hnorm x) := by
  unfold equivACris
  rw [AdicCompletion.evalₐ_ringEquivOfRingEquiv, hx, AdicCompletion.powQuotientEquiv_mk]

@[simp]
theorem equivACris_algebraMap (x : A0 C p) :
    equivACris p e d hd hnorm (algebraMap (A0 C p) (ACris C p) x) =
      algebraMap (A0 C' p) (ACris C' p) (equivA0 p e d hd hnorm x) :=
  AdicCompletion.ringEquivOfRingEquiv_algebraMap I I' (equivA0 p e d hd hnorm)
    (equivA0_map_span_prime p e d hd hnorm) x

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
