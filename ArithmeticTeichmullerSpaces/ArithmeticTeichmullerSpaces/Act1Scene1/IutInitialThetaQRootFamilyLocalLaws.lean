import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootFamily

/-!
source-id: JT-SCENE1-INITIAL-THETA-QROOT-FAMILY-LOCAL-LAWS
source: `refer/iut/Iut/Concrete/ThetaRegion.lean`, `ThetaLocalData.qroot_pow`,
`ordp_qroot`, `residueChar_mem`, and `bad_residueChar_mem`; Joshi III
`ss:theta-data-fixing2` and the local Tate parameters in `cor:cor312`.
fidelity: proves the actual family's local laws for every base bad place below
a torsion-field place, using contraction uniqueness and the canonical completion
map. No base-place equality, root equation, or order certificate is an input.
The family retains the full odd support; no support-coverage, paper-locus, or
Bloch--Kato identification is asserted. Original proofs; no reference code copied.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaQRootFamily

open JoshiTeich.Prologue
open NumberField

universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem mem_badFinset_of_liesOver
    {v : FinitePlace ↥D.prime.torsionField} {w : FinitePlace D.F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    v ∈ (iutInitialThetaOddSupportTorsionQRootSource D).badFinset := by
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  change v ∈ iutBadPlacesOverFinset (k := D.F) (K := ↥D.prime.torsionField)
    B.badPlaces B.badPlaces_finite
  exact (mem_iutBadPlacesOverFinset_iff B.badPlaces B.badPlaces_finite v).mpr
    ⟨w, iutBadPlacesOver_subset_oddMultiplicativeSupport D hw, hvw⟩

theorem qrootAt_pow_eq_of_liesOver
    {v : FinitePlace ↥D.prime.torsionField} {w : FinitePlace D.F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    qrootAt D v ^ (2 * D.prime.ℓ) =
      iutEmbedCompletion hvw (D.prime.tate w hw).q := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let s : R.badFinset := ⟨v, mem_badFinset_of_liesOver D hvw hw⟩
  have hbase : (R.basePlace s).1 = w :=
    (iutPlaceUnder_eq_of_liesOver (R.liesOver s)).trans
      (iutPlaceUnder_eq_of_liesOver hvw).symm
  have hwBase : (R.basePlace s).1 ∈
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := hbase.symm ▸ hw
  have h := qrootAt_pow_eq_admissiblePrime D v s.2 hwBase
  have hmap : R.completionMap s = iutEmbedCompletion (R.liesOver s) := rfl
  change qrootAt D v ^ (2 * D.prime.ℓ) =
    R.completionMap s (D.prime.tate (R.basePlace s).1 hwBase).q at h
  rw [hmap] at h
  have transport (b : FinitePlace D.F)
      (hvb : Ideal.LiesOver v.maximalIdeal.asIdeal b.maximalIdeal.asIdeal)
      (hb : b ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad)
      (hbw : b = w) :
      iutEmbedCompletion hvb (D.prime.tate b hb).q =
        iutEmbedCompletion hvw (D.prime.tate w hw).q := by
    subst b
    rfl
  exact h.trans (transport (R.basePlace s).1 (R.liesOver s) hwBase hbase)

theorem qrootAt_ordp_eq_of_liesOver
    {v : FinitePlace ↥D.prime.torsionField} {w : FinitePlace D.F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    Arithmetic.ordp v (qrootAt D v) =
      (D.prime.qOrder w hw : ℝ) /
        (2 * (D.prime.ℓ : ℝ) * Arithmetic.ramIdx w) := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let s : R.badFinset := ⟨v, mem_badFinset_of_liesOver D hvw hw⟩
  have hbase : (R.basePlace s).1 = w :=
    (iutPlaceUnder_eq_of_liesOver (R.liesOver s)).trans
      (iutPlaceUnder_eq_of_liesOver hvw).symm
  have hwBase : (R.basePlace s).1 ∈
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := hbase.symm ▸ hw
  have h := qrootAt_ordp_eq_baseQOrder D v s.2
  rw [iutInitialThetaOddSupportBaseQPilotSource_qOrder_eq_admissiblePrime
    D (R.basePlace s) hwBase] at h
  have transport (b : FinitePlace D.F)
      (hb : b ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad)
      (hbw : b = w) :
      (D.prime.qOrder b hb : ℝ) / (2 * (D.prime.ℓ : ℝ) * Arithmetic.ramIdx b) =
        (D.prime.qOrder w hw : ℝ) / (2 * (D.prime.ℓ : ℝ) * Arithmetic.ramIdx w) := by
    subst b
    rfl
  exact h.trans (transport (R.basePlace s).1 hwBase hbase)

theorem residueChar_mem_badChars_of_liesOver
    {v : FinitePlace ↥D.prime.torsionField} {w : FinitePlace D.F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    Arithmetic.residueChar v ∈ badChars D :=
  residueChar_mem_badChars_of_mem_badFinset D v
    (mem_badFinset_of_liesOver D hvw hw)

theorem bad_residueChar_mem_badChars
    (w : FinitePlace D.F)
    (hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    Arithmetic.residueChar w ∈ badChars D := by
  obtain ⟨v, hvw⟩ := JoshiTeich.ReferenceIut.FinitePlace.exists_liesOver
    (K := ↥D.prime.torsionField) w
  rw [← Arithmetic.residueChar_eq_of_liesOver hvw]
  exact residueChar_mem_badChars_of_liesOver D hvw hw

end
end JoshiTeich.Act1Scene1.IutInitialThetaQRootFamily
