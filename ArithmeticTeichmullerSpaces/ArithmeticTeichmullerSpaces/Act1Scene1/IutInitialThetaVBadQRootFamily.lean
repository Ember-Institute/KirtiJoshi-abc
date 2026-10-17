import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootFamilyLocalLaws

/-!
source-id: JT-SCENE1-INITIAL-THETA-VBAD-QROOT-FAMILY
source: `refer/iut/Iut/Concrete/ThetaRegion.lean`, `ThetaLocalData`, and
`refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean`, `sum_weight_ordp_qroot`;
Joshi III `ss:theta-data-fixing2` and its local Tate parameters.
fidelity: restricts the existing full-support root family to the actual VBad
over-locus, taking 1 elsewhere. The unfiltered torsion-place fiber sum recovers
the actual VBad q-pilot, without assuming full odd support equals VBad. The two
root choices are compared only by their orders, not by element equality.
Original proofs; no reference source code copied.
boundary: Scene1/Derived; no paper representative or theta/BK identity.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaQRootFamily

open JoshiTeich.Prologue
open NumberField
open scoped BigOperators

universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def vbadQrootAt (v : FinitePlace ↥D.prime.torsionField) :
    v.maximalIdeal.adicCompletion ↥D.prime.torsionField := by
  classical
  exact if v ∈ (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset then
    qrootAt D v else 1

theorem vbadQrootAt_ne_zero (v : FinitePlace ↥D.prime.torsionField) :
    vbadQrootAt D v ≠ 0 := by
  classical
  unfold vbadQrootAt
  split_ifs
  · exact qrootAt_ne_zero D v
  · exact one_ne_zero

theorem vbadQrootAt_ordp_nonneg (v : FinitePlace ↥D.prime.torsionField) :
    0 ≤ Arithmetic.ordp v (vbadQrootAt D v) := by
  classical
  unfold vbadQrootAt
  split_ifs
  · exact qrootAt_ordp_nonneg D v
  · simp [Arithmetic.ordp]

theorem vbadQrootAt_eq_one_of_residueChar_not_mem_badChars
    (v : FinitePlace ↥D.prime.torsionField)
    (hv : Arithmetic.residueChar v ∉ badChars D) :
    vbadQrootAt D v = 1 := by
  classical
  unfold vbadQrootAt
  split_ifs
  · exact qrootAt_eq_one_of_residueChar_not_mem_badChars D v hv
  · rfl

theorem vbadQrootAt_eq_qrootAt_of_liesOver
    {v : FinitePlace ↥D.prime.torsionField} {w : FinitePlace D.F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    vbadQrootAt D v = qrootAt D v := by
  classical
  let B := IutBaseQPilotSource.ofInitialThetaData D
  have hv : v ∈ (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset := by
    change v ∈ iutBadPlacesOverFinset (k := D.F) (K := ↥D.prime.torsionField)
      B.badPlaces B.badPlaces_finite
    exact (mem_iutBadPlacesOverFinset_iff B.badPlaces B.badPlaces_finite v).mpr
      ⟨w, hw, hvw⟩
  simp only [vbadQrootAt, ite_eq_left hv]

theorem vbadQrootAt_pow_eq_of_liesOver
    {v : FinitePlace ↥D.prime.torsionField} {w : FinitePlace D.F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    vbadQrootAt D v ^ (2 * D.prime.ℓ) =
      iutEmbedCompletion hvw (D.prime.tate w hw).q := by
  rw [vbadQrootAt_eq_qrootAt_of_liesOver D hvw hw]
  exact qrootAt_pow_eq_of_liesOver D hvw hw

theorem vbadQrootAt_ordp_eq_of_liesOver
    {v : FinitePlace ↥D.prime.torsionField} {w : FinitePlace D.F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    Arithmetic.ordp v (vbadQrootAt D v) =
      (D.prime.qOrder w hw : ℝ) /
        (2 * (D.prime.ℓ : ℝ) * Arithmetic.ramIdx w) := by
  rw [vbadQrootAt_eq_qrootAt_of_liesOver D hvw hw]
  exact qrootAt_ordp_eq_of_liesOver D hvw hw

theorem qrootAt_ordp_eq_canonicalVBadRoot
    (s : (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset) :
    Arithmetic.ordp s.1 (qrootAt D s.1) =
      Arithmetic.ordp s.1
        ((IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).qroot s) := by
  let B := IutBaseQPilotSource.ofInitialThetaData D
  let R := IutTorsionQRootSource.ofInitialThetaDataFromGlobal D
  have hw : (R.basePlace s).1 ∈
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
    B.mem_badPlaces (R.basePlace s)
  have hfull := qrootAt_pow_eq_of_liesOver D (R.liesOver s) hw
  have hcanonical := R.qroot_pow_eq s
  have hmap : R.completionMap s = iutEmbedCompletion (R.liesOver s) := rfl
  have hparam : B.tateParameter (R.basePlace s) =
      (D.prime.tate (R.basePlace s).1 hw).q := rfl
  rw [hmap, hparam] at hcanonical
  have h := congrArg (Arithmetic.ordp s.1) (hfull.trans hcanonical.symm)
  rw [Arithmetic.ordp_pow, Arithmetic.ordp_pow] at h
  have hn : ((2 * D.prime.ℓ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (by decide : (2 : ℕ) ≠ 0) D.prime.ℓ_prime.ne_zero)
  exact mul_left_cancel₀ hn h

/-- The sum uses every torsion-field place above p; no bad-place indicator
is present in the summand. -/
def vbadWeightedFiber (p : ℕ) : ℝ := by
  letI : Finite {v : FinitePlace ↥D.prime.torsionField //
    Arithmetic.residueChar v = p} := Arithmetic.fiber_finite p
  letI : Fintype {v : FinitePlace ↥D.prime.torsionField //
    Arithmetic.residueChar v = p} := Fintype.ofFinite _
  exact ∑ v : {v : FinitePlace ↥D.prime.torsionField // Arithmetic.residueChar v = p},
    Arithmetic.placeWeight v.1 * Arithmetic.ordp v.1 (vbadQrootAt D v.1)

theorem vbadWeightedFiber_eq_canonical (p : ℕ) :
    vbadWeightedFiber D p =
      IutTorsionQRootSource.canonical_qroot_weighted_fiber_of_initialThetaData D p := by
  classical
  letI : Finite {v : FinitePlace ↥D.prime.torsionField //
    Arithmetic.residueChar v = p} := Arithmetic.fiber_finite p
  letI : Fintype {v : FinitePlace ↥D.prime.torsionField //
    Arithmetic.residueChar v = p} := Fintype.ofFinite _
  let R := IutTorsionQRootSource.ofInitialThetaDataFromGlobal D
  change (∑ v : {v : FinitePlace ↥D.prime.torsionField // Arithmetic.residueChar v = p},
      Arithmetic.placeWeight v.1 * Arithmetic.ordp v.1 (vbadQrootAt D v.1)) =
    ∑ v : {v : FinitePlace ↥D.prime.torsionField // Arithmetic.residueChar v = p},
      Arithmetic.placeWeight v.1 *
        (if hv : v.1 ∈ R.badFinset then Arithmetic.ordp v.1 (R.qroot ⟨v.1, hv⟩) else 0)
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v.1 ∈ R.badFinset
  · have hv' : v.1 ∈ (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset := hv
    rw [dite_eq_left hv]
    simp only [vbadQrootAt, ite_eq_left hv']
    rw [qrootAt_ordp_eq_canonicalVBadRoot D ⟨v.1, hv⟩]
  · have hv' : v.1 ∉ (IutTorsionQRootSource.ofInitialThetaDataFromGlobal D).badFinset := hv
    rw [dite_eq_right hv]
    simp [vbadQrootAt, hv', Arithmetic.ordp]

theorem vbadWeightedFiber_eq_qOrderSum (p : ℕ)
    (bad : Finset (FinitePlace D.F))
    (hbad : (↑bad : Set (FinitePlace D.F)) =
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    vbadWeightedFiber D p =
      ∑ w ∈ bad.attach.filter (fun w => Arithmetic.residueChar w.1 = p),
        Arithmetic.qPilotWeight w.1 *
          (D.prime.qOrder w.1 (hbad ▸ Finset.mem_coe.mpr w.2) : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := by
  classical
  letI : Finite {v : FinitePlace ↥D.prime.torsionField //
    Arithmetic.residueChar v = p} := Arithmetic.fiber_finite p
  letI : Fintype {v : FinitePlace ↥D.prime.torsionField //
    Arithmetic.residueChar v = p} := Fintype.ofFinite _
  have hcanonical :
      IutTorsionQRootSource.canonical_qroot_weighted_fiber_of_initialThetaData D p =
        ∑ w ∈ bad.filter (fun w => Arithmetic.residueChar w = p),
          (Arithmetic.inertDeg w : ℝ) / Module.finrank ℚ D.F *
            (if hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad then
              (D.prime.qOrder w hw : ℝ) / (2 * (D.prime.ℓ : ℝ)) else 0) :=
    IutTorsionQRootSource.canonical_qroot_weighted_sum_of_initialThetaData D p bad hbad
  rw [vbadWeightedFiber_eq_canonical, hcanonical, Finset.sum_filter,
    ← Finset.sum_attach, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  have hw : w.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
    hbad ▸ Finset.mem_coe.mpr w.2
  by_cases hp : Arithmetic.residueChar w.1 = p
  · simp only [ite_eq_left hp, dite_eq_left hw]
    unfold Arithmetic.qPilotWeight
    ring
  · simp only [ite_eq_right hp]

theorem vbadWeighted_logSum_eq_iut_absLogQ :
    (∑ p ∈ (IutTorsionQRootSource.iutInitialThetaQPilotData D).badFinset.image
        Arithmetic.residueChar, Real.log p * vbadWeightedFiber D p) =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  simp_rw [vbadWeightedFiber_eq_canonical]
  exact IutTorsionQRootSource.canonical_qroot_log_sum_eq_iut_absLogQ D

end
end JoshiTeich.Act1Scene1.IutInitialThetaQRootFamily
