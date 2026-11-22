import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option autoImplicit false

namespace AdicCompletion

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

private theorem factorPow_evalₐ_eq (z : AdicCompletion I R) {m n : ℕ} (hmn : m ≤ n) :
    Ideal.Quotient.factorPow I hmn (evalₐ I n z) = evalₐ I m z := by
  obtain ⟨a, rfl⟩ := mk_surjective I R z
  rw [evalₐ_mk, Ideal.Quotient.factor_mk, evalₐ_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hmn a

private theorem quotientMaps_compatible (q : (n : ℕ) → (R ⧸ I ^ n) →+* S ⧸ J ^ n)
    (hq : ∀ {m n : ℕ} (hmn : m ≤ n) (z : R ⧸ I ^ n),
      Ideal.Quotient.factorPow J hmn (q n z) = q m (Ideal.Quotient.factorPow I hmn z))
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow J hmn).comp ((q n).comp (evalₐ I n).toRingHom) =
      (q m).comp (evalₐ I m).toRingHom := by
  apply RingHom.ext
  intro z
  change Ideal.Quotient.factorPow J hmn (q n (evalₐ I n z)) = q m (evalₐ I m z)
  rw [hq hmn, factorPow_evalₐ_eq I z hmn]

private def liftQuotientMaps (q : (n : ℕ) → (R ⧸ I ^ n) →+* S ⧸ J ^ n)
    (hq : ∀ {m n : ℕ} (hmn : m ≤ n) (z : R ⧸ I ^ n),
      Ideal.Quotient.factorPow J hmn (q n z) = q m (Ideal.Quotient.factorPow I hmn z)) :
    AdicCompletion I R →+* AdicCompletion J S :=
  liftRingHom J (fun n => (q n).comp (evalₐ I n).toRingHom) (quotientMaps_compatible I J q hq)

private theorem evalₐ_liftQuotientMaps (q : (n : ℕ) → (R ⧸ I ^ n) →+* S ⧸ J ^ n)
    (hq : ∀ {m n : ℕ} (hmn : m ≤ n) (z : R ⧸ I ^ n),
      Ideal.Quotient.factorPow J hmn (q n z) = q m (Ideal.Quotient.factorPow I hmn z))
    (n : ℕ) (z : AdicCompletion I R) :
    evalₐ J n (liftQuotientMaps I J q hq z) = q n (evalₐ I n z) :=
  evalₐ_liftRingHom J (fun n => (q n).comp (evalₐ I n).toRingHom)
    (quotientMaps_compatible I J q hq) n z

variable (e : R ≃+* S) (he : J = I.map e.toRingHom)
include he

/-- A ring equivalence gives an equivalence of the quotients by corresponding ideal powers. -/
def powQuotientEquiv (n : ℕ) : R ⧸ I ^ n ≃+* S ⧸ J ^ n :=
  Ideal.quotientEquiv (I ^ n) (J ^ n) e (by
    change J ^ n = (I ^ n).map e.toRingHom
    exact (congrArg (fun K : Ideal S => K ^ n) he).trans (Ideal.map_pow e.toRingHom I n).symm)

@[simp]
theorem powQuotientEquiv_mk (n : ℕ) (x : R) :
    powQuotientEquiv I J e he n (Ideal.Quotient.mk (I ^ n) x) =
      Ideal.Quotient.mk (J ^ n) (e x) :=
  rfl

theorem factorPow_powQuotientEquiv {m n : ℕ} (hmn : m ≤ n) (z : R ⧸ I ^ n) :
    Ideal.Quotient.factorPow J hmn (powQuotientEquiv I J e he n z) =
      powQuotientEquiv I J e he m (Ideal.Quotient.factorPow I hmn z) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [powQuotientEquiv_mk, Ideal.Quotient.factor_mk]

private theorem factorPow_powQuotientEquiv_symm {m n : ℕ} (hmn : m ≤ n)
    (z : S ⧸ J ^ n) :
    Ideal.Quotient.factorPow I hmn ((powQuotientEquiv I J e he n).symm z) =
      (powQuotientEquiv I J e he m).symm (Ideal.Quotient.factorPow J hmn z) := by
  apply (powQuotientEquiv I J e he m).injective
  have h := factorPow_powQuotientEquiv I J e he hmn ((powQuotientEquiv I J e he n).symm z)
  simpa only [RingEquiv.apply_symm_apply] using h.symm

private def completionToTarget : AdicCompletion I R →+* AdicCompletion J S :=
  liftQuotientMaps I J (fun n => (powQuotientEquiv I J e he n).toRingHom)
    (fun h z => factorPow_powQuotientEquiv I J e he h z)

private def completionFromTarget : AdicCompletion J S →+* AdicCompletion I R :=
  liftQuotientMaps J I (fun n => (powQuotientEquiv I J e he n).symm.toRingHom)
    (fun h z => factorPow_powQuotientEquiv_symm I J e he h z)

private theorem evalₐ_completionToTarget (n : ℕ) (z : AdicCompletion I R) :
    evalₐ J n (completionToTarget I J e he z) =
      powQuotientEquiv I J e he n (evalₐ I n z) :=
  evalₐ_liftQuotientMaps I J (fun n => (powQuotientEquiv I J e he n).toRingHom)
    (fun h x => factorPow_powQuotientEquiv I J e he h x) n z

private theorem evalₐ_completionFromTarget (n : ℕ) (z : AdicCompletion J S) :
    evalₐ I n (completionFromTarget I J e he z) =
      (powQuotientEquiv I J e he n).symm (evalₐ J n z) :=
  evalₐ_liftQuotientMaps J I (fun n => (powQuotientEquiv I J e he n).symm.toRingHom)
    (fun h x => factorPow_powQuotientEquiv_symm I J e he h x) n z

/-- A ring equivalence induces a ring equivalence on the completions at corresponding ideals. -/
def ringEquivOfRingEquiv : AdicCompletion I R ≃+* AdicCompletion J S where
  __ := completionToTarget I J e he
  invFun := completionFromTarget I J e he
  left_inv z := by
    apply ext_evalₐ
    intro n
    change evalₐ I n (completionFromTarget I J e he (completionToTarget I J e he z)) = _
    rw [evalₐ_completionFromTarget, evalₐ_completionToTarget, RingEquiv.symm_apply_apply]
  right_inv z := by
    apply ext_evalₐ
    intro n
    change evalₐ J n (completionToTarget I J e he (completionFromTarget I J e he z)) = _
    rw [evalₐ_completionToTarget, evalₐ_completionFromTarget, RingEquiv.apply_symm_apply]

theorem evalₐ_ringEquivOfRingEquiv (n : ℕ) (z : AdicCompletion I R) :
    evalₐ J n (ringEquivOfRingEquiv I J e he z) = powQuotientEquiv I J e he n (evalₐ I n z) :=
  evalₐ_completionToTarget I J e he n z

@[simp]
theorem ringEquivOfRingEquiv_algebraMap (x : R) :
    ringEquivOfRingEquiv I J e he (algebraMap R (AdicCompletion I R) x) =
      algebraMap S (AdicCompletion J S) (e x) := by
  apply ext_evalₐ
  intro n
  change evalₐ J n (ringEquivOfRingEquiv I J e he (of I R x)) = evalₐ J n (of J S (e x))
  simp only [evalₐ_ringEquivOfRingEquiv, evalₐ_of, powQuotientEquiv_mk]

end

end AdicCompletion
