import Solutions.Source_ReferenceIutCor312CrystallineResidueOrbit
import Solutions.Source_ReferenceIutCor312CrystallineTopology

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open CrystallineEnvelope
open scoped Topology CrystallineEnvelope

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] [CharZero K]
variable (p : ℕ) [Fact p.Prime]
variable [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "C" => Field K
local notation "G" => (Algebraic K ≃ₐ[K] Algebraic K)
local notation "D" => A0 C p
local notation "A" => ACris C p
local notation "I" => (Ideal.span {(p : D)} : Ideal D)

private theorem eval_extendGaloisACris_eq_of_eval_eq
    (σ : G) (k : ℕ) (z w : A)
    (h : AdicCompletion.evalₐ I k z = AdicCompletion.evalₐ I k w) :
    AdicCompletion.evalₐ I k (extendGaloisACris p σ z) =
      AdicCompletion.evalₐ I k (extendGaloisACris p σ w) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I k w)
  have hz := eval_mapACris_of_eq C p (extendGaloisA0 p σ) k z a (h.trans ha.symm)
  have hw := eval_mapACris_of_eq C p (extendGaloisA0 p σ) k w a ha.symm
  exact hz.trans hw.symm

/-- The original Galois action is jointly continuous on the crystalline
completion for the Krull and prime-adic topologies. -/
theorem continuous_extendGaloisACris :
    Continuous (fun x : G × A => extendGaloisACris p x.1 x.2) := by
  apply (continuous_into_ACris_iff_eventually_evalₐ_eq C p _).mpr
  intro x k
  have h₁ := (eval_extendGaloisACris_isLocallyConstant p k x.2).eventually_eq x.1
  have h₂ := (continuous_into_ACris_iff_eventually_evalₐ_eq C p (fun z : A => z)).mp
    continuous_id x.2 k
  have hf : ContinuousAt (fun y : G × A => y.1) x := continuous_fst.continuousAt
  have hs : ContinuousAt (fun y : G × A => y.2) x := continuous_snd.continuousAt
  filter_upwards [hf.eventually h₁, hs.eventually h₂] with y hy₁ hy₂
  exact (eval_extendGaloisACris_eq_of_eval_eq p y.1 k y.2 x.2 hy₂).trans hy₁

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
