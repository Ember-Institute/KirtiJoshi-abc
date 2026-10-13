import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRepresentativeTerm
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedFieldOrientation

/-!
source-id: JT-SCENE1-INITIAL-THETA-REPRESENTATIVE-QROOT-SUM
source: the actual selected q-root power equation, canonical section Tate
parameters, completion valuation, and the actual representative terms.
fidelity: identifies the two finite sums without independent theta/packet/hull
payloads or a sum-equality certificate. It preserves absolute ramification in
the paper-normalized term. Source-to-section mapping for the q-pilot bound
remains explicit; no theta-volume estimate is asserted.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

private def selectedRepresentativeEquiv
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D} ≃
      (iutInitialThetaOddTateSectionTateParameterData D).places where
  toFun s := ⟨s.1.1,
    (iutInitialThetaOddSupportSelectedQRootPlaces_finite D).mem_toFinset.mpr s.2⟩
  invFun w := ⟨⟨w.1, by
    have hw := (iutInitialThetaOddSupportSelectedQRootPlaces_finite D).mem_toFinset.mp w.2
    rcases hw with ⟨v, hv, h⟩
    rw [← h]
    exact (iutInitialThetaOddSupportSelectedQRootPlace D v hv).2⟩,
    (iutInitialThetaOddSupportSelectedQRootPlaces_finite D).mem_toFinset.mp w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem selectedRoot_term_eq
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (s : {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
      s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}) :
    ((Arithmetic.ramIdx s.1.1 : ℝ) * Arithmetic.ordp s.1.1
      ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s.1)) *
        Real.log (Arithmetic.residueChar s.1.1) =
      iutInitialThetaSectionRepresentativeTerm D s.1.1 := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let w := selectedRepresentativeEquiv D s
  have hAt : iutInitialThetaOddSupportSelectedQRootAt D w = s.1 := by
    apply Subtype.ext
    rfl
  have hpow : R.qroot s.1 ^ (2 * D.prime.ℓ) =
      (iutInitialThetaOddTateSectionTateParameterData D).parameter s.1.1 := by
    have h := iutInitialThetaOddSupportSelectedQRootQRoot_pow_eq_sectionParameter D w
    have hroot : iutInitialThetaOddSupportSelectedQRootQRoot D w = R.qroot s.1 := by
      unfold iutInitialThetaOddSupportSelectedQRootQRoot
      exact eq_of_heq (by cases hAt; rfl)
    rw [hroot] at h
    exact h
  let q := (iutInitialThetaOddTateSectionTateParameterData D).parameter s.1.1
  have hlaws := iutInitialThetaOddTateSectionTateParameterData_laws D
  have hvalued := iutCompletionQOrder_valued s.1.1 q
    (hlaws.parameter_nonzero w.1 w.2) (by
      change ‖(iutInitialThetaOddTateSectionTateParameterData D).parameter w.1‖ < 1
      rw [← hlaws.norm_eq w.1 w.2]
      exact hlaws.norm_lt_one w.1 w.2)
  have hord := Arithmetic.ordp_eq_of_valued s.1.1 q
    (-(iutCompletionQOrder s.1.1 q : ℤ)) hvalued
  have hpower := congrArg (Arithmetic.ordp s.1.1) hpow
  rw [Arithmetic.ordp_pow, hord] at hpower
  push_cast at hpower
  have hEll : (D.prime.ℓ : ℝ) ≠ 0 := by
    have h := D.prime.five_le
    positivity
  have hRam : (Arithmetic.ramIdx s.1.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.ramIdx_pos s.1.1).ne'
  have hlocal : (Arithmetic.ramIdx s.1.1 : ℝ) * Arithmetic.ordp s.1.1 (R.qroot s.1) =
      (iutCompletionQOrder s.1.1 q : ℝ) / (2 * (D.prime.ℓ : ℝ)) := by
    field_simp [hEll, hRam] at hpower ⊢
    nlinarith [hpower]
  unfold iutInitialThetaSectionRepresentativeTerm
  change _ = (iutCompletionQOrder s.1.1 q : ℝ) /
    (2 * (D.prime.ℓ : ℝ)) * Real.log (Arithmetic.residueChar s.1.1)
  rw [hlocal]

def iutInitialThetaSelectedQRootPaperSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) : ℝ :=
  let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  letI : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  ∑ s : S, ((Arithmetic.ramIdx s.1.1 : ℝ) * Arithmetic.ordp s.1.1
    ((iutInitialThetaOddSupportTorsionQRootSource D).qroot s.1)) *
      Real.log (Arithmetic.residueChar s.1.1)

theorem iutInitialThetaSelectedQRootPaperSum_eq_representativeSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    iutInitialThetaSelectedQRootPaperSum D =
      ∑ w : (iutInitialThetaOddTateSectionTateParameterData D).places,
        iutInitialThetaSectionRepresentativeTerm D w.1 := by
  let S := {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}
  let : Fintype S := (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype
  unfold iutInitialThetaSelectedQRootPaperSum
  let e := selectedRepresentativeEquiv D
  calc
    _ = ∑ s, iutInitialThetaSectionRepresentativeTerm D (e s).1 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact selectedRoot_term_eq D s
    _ = _ := e.sum_comp (fun w => iutInitialThetaSectionRepresentativeTerm D w.1)

theorem iutInitialThetaSelectedQRootPaperSum_pos
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    0 < iutInitialThetaSelectedQRootPaperSum D := by
  rw [iutInitialThetaSelectedQRootPaperSum_eq_representativeSum]
  exact iutInitialThetaSectionRepresentativeSum_pos D

theorem Corollary312QPilotData.absLogQ_le_initialThetaSelectedQRootPaperSum
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data D.F O p} (P : Corollary312QPilotData p T)
    (f : P.badFinset → (iutInitialThetaOddTateSectionTateParameterData D).places)
    (hTerm : ∀ w : P.badFinset,
      -Real.log (Corollary312PaperNormalizedSourceQFactor p T
        ⟨w.1, P.mem_bad p w.2⟩) = iutInitialThetaSectionRepresentativeTerm D (f w).1)
    (hPrime : ∀ w : P.badFinset,
      Arithmetic.residueChar w.1 = Arithmetic.residueChar (f w).1)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hRaw : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : T.ell = D.prime.ℓ) :
    P.absLogQ p ≤ iutInitialThetaSelectedQRootPaperSum D := by
  rw [iutInitialThetaSelectedQRootPaperSum_eq_representativeSum]
  exact P.absLogQ_le_initialThetaSectionRepresentativeSum D p f hTerm hPrime hOrder hRaw hEll

end
end JoshiTeich.Act1Scene1
