import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompletionSource

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators NumberField

universe u

/-!
source-id: IUT-COR312-QROOT-WEIGHTED-ACCOUNTING
source: `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean:339-376`
(`ThetaLocalData.sum_weight_ordp_qroot`), together with
`refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:245-276`
(`sum_localDeg_liesOver`).
fidelity: the canonical q-root source is extended by zero away from its
over-locus, then the finite-place weighted sum is reduced to the base support.
The Tate valuation law and q-root existence remain explicit inputs.
boundary: Scene1/Derived
-/

namespace IutTorsionQRootSource

variable {F Kt : Type u} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
variable [Algebra F Kt] {ell : ℕ} {B : IutBaseQPilotSource F ell}

theorem canonical_qroot_weighted_sum
    (p : ℕ)
    [Fintype {v : NumberField.FinitePlace Kt // Arithmetic.residueChar v = p}]
    (bad : Finset (NumberField.FinitePlace F))
    (hbad : (↑bad : Set (NumberField.FinitePlace F)) = B.badPlaces)
    (c : NumberField.FinitePlace F → ℝ)
    (hc : ∀ w : B.badFinset,
      c w.1 = (B.qOrder w : ℝ) / (2 * (ell : ℝ)))
    (qroot : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite, v.1.maximalIdeal.adicCompletion Kt)
    (qroot_pow_eq : ∀ v : iutBadPlacesOverFinset (k := F) (K := Kt) B.badPlaces
      B.badPlaces_finite,
      qroot v ^ (2 * ell) =
        iutEmbedCompletion (basePlaceOf_liesOver (B := B) v)
          (B.tateParameter (basePlaceOf (B := B) v)))
    (hTateValued : ∀ v : B.badFinset,
      Valued.v (B.tateParameter v) = exp (-(B.qOrder v : ℤ)))
    (hEll : 0 < ell) :
    ∑ v : {v : NumberField.FinitePlace Kt // Arithmetic.residueChar v = p},
        Arithmetic.placeWeight v.1 *
          (if hv : v.1 ∈ iutBadPlacesOverFinset B.badPlaces
              B.badPlaces_finite then
            Arithmetic.ordp v.1 (qroot ⟨v.1, hv⟩)
          else 0) =
      ∑ w ∈ bad.filter (fun w => Arithmetic.residueChar w = p),
        (Arithmetic.inertDeg w : ℝ) / Module.finrank ℚ F * c w := by
  let carrier := iutBadPlacesOverFinset (k := F) (K := Kt)
    B.badPlaces B.badPlaces_finite
  let o : NumberField.FinitePlace Kt → ℝ := fun v =>
    if hv : v ∈ carrier then Arithmetic.ordp v (qroot ⟨v, hv⟩) else 0
  have ho : ∀ v w,
      Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal →
        w ∈ B.badPlaces → o v = c w / Arithmetic.ramIdx w := by
    intro v w hvw hw
    have hvC : v ∈ carrier := by
      apply (mem_iutBadPlacesOverFinset_iff B.badPlaces B.badPlaces_finite v).mpr
      exact ⟨w, hw, hvw⟩
    let vC : carrier := ⟨v, hvC⟩
    have hbase : (basePlaceOf (B := B) vC).1 = w := by
      calc
        (basePlaceOf (B := B) vC).1 = iutPlaceUnder v :=
          basePlaceOf_eq_placeUnder (B := B) vC
        _ = w := (iutPlaceUnder_eq_of_liesOver hvw).symm
    have hbase' : basePlaceOf (B := B) vC =
        ⟨w, (Set.ext_iff.mp B.badFinset_spec w).mpr hw⟩ := by
      apply Subtype.ext
      exact hbase
    have hOrd := canonical_qroot_ordp_eq B qroot qroot_pow_eq
      hTateValued hEll vC
    calc
      o v = Arithmetic.ordp v (qroot vC) := by
        simp only [o, carrier, dif_pos hvC]
      _ = (B.qOrder (basePlaceOf (B := B) vC) : ℝ) /
          (2 * (ell : ℝ) * Arithmetic.ramIdx (basePlaceOf (B := B) vC).1) := hOrd
      _ = (B.qOrder (⟨w, (Set.ext_iff.mp B.badFinset_spec w).mpr hw⟩) : ℝ) /
          (2 * (ell : ℝ) * Arithmetic.ramIdx w) := by rw [hbase']
      _ = c w / Arithmetic.ramIdx w := by
        rw [hc]
        ring
  have ho0 : ∀ v, (∀ w ∈ B.badPlaces,
      ¬ Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal) → o v = 0 := by
    intro v hnone
    have hvC : ¬ v ∈ carrier := by
      intro hv
      obtain ⟨w, hw, hvw⟩ :=
        (mem_iutBadPlacesOverFinset_iff B.badPlaces B.badPlaces_finite v).mp hv
      exact hnone w hw hvw
    simp [o, hvC]
  have hSum := Arithmetic.sum_placeWeight_mul (L := Kt) (F := F) p
    B.badPlaces bad hbad c o ho ho0
  simpa [o, carrier] using hSum

end IutTorsionQRootSource

end JoshiTeich.Act1Scene1
