import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationInertia
import ArithmeticTeichmullerSpaces.Act1Scene1.NormalizationPrimeValuation

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the existing normalization lying-over theorem and Dedekind prime spectrum.
fidelity: lifts a maximal ideal with a specified polynomial-base center along
the original normalization inclusion, retaining its contraction and center.
Original composition of existing project proofs; no reference code copied.
boundary: the actual seed consumer supplies the original closed prime and
center; this generic result asserts no cusp or arithmetic stabilizer identity.
-/

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open IsDedekindDomain
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section
variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
variable {t : Ω} {F N : IntermediateField (rationalBase k t) Ω}
variable [FiniteDimensional (rationalBase k t) N]
  [Algebra.IsSeparable (rationalBase k t) N]

/-- Lift a closed centered prime to a nonzero prime of the same normalization. -/
theorem exists_heightOne_over_center
    (ht : Transcendental k t) (hFN : F ≤ N)
    (w : Ideal (coordRing t F)) (hw : w.IsMaximal)
    (c : polynomialBase k t)
    (hc : algebraMap (polynomialBase k t) (coordRing t F) c ∈ w) :
    ∃ p : HeightOneSpectrum (coordRing t N),
      p.asIdeal.IsMaximal ∧ p.asIdeal.comap (ringMap hFN) = w ∧
      algebraMap (polynomialBase k t) (coordRing t N) c ∈ p.asIdeal := by
  obtain ⟨P, hP, hPw⟩ := normalization_exists_maximal_over hFN w hw
  have hP0 : P ≠ ⊥ := by
    intro h
    have hbot : (⊥ : Ideal (coordRing t N)).IsMaximal := h ▸ hP
    exact notFieldRing t ht N (Ring.isField_iff_maximal_bot.mpr hbot)
  let p : HeightOneSpectrum (coordRing t N) := ⟨P, hP.isPrime, hP0⟩
  refine ⟨p, hP, hPw, ?_⟩
  have hm : ringMap hFN (algebraMap (polynomialBase k t) (coordRing t F) c) ∈ P := by
    change algebraMap (polynomialBase k t) (coordRing t F) c ∈ P.comap (ringMap hFN)
    rw [hPw]
    exact hc
  exact hm


/-- Transport the inertia criterion from a lift back to the original contracted prime. -/
theorem ramificationIdx_one_of_prime_lift [CharZero k]
    [IsGalois (rationalBase k t) N]
    {L : IntermediateField (rationalBase k t) Ω}
    (ht : Transcendental k t) (hFL : F ≤ L) (hLN : L ≤ N)
    (w : Ideal (coordRing t L)) (p : HeightOneSpectrum (coordRing t N))
    (hp : p.asIdeal.IsMaximal) (hpw : p.asIdeal.comap (ringMap hLN) = w)
    (hi : p.asIdeal.inertia (N ≃ₐ[rationalBase k t] N) ⊓ fixSub N F ≤ fixSub N L) :
    (letI := ringMapAlgebra hFL
     w.ramificationIdx (coordRing t F)) = 1 := by
  letI : p.asIdeal.IsMaximal := hp
  have hr := (ramificationIdx_eq_one_iff ht hFL hLN p.asIdeal).mpr hi
  rw [hpw] at hr
  exact hr

end
end JoshiTeich.Act1Scene1.FunctionFieldNormalization
