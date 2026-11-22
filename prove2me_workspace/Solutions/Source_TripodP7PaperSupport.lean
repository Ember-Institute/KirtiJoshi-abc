import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompat.Cor312.ThetaData.ValuationTransfer
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PlaceUnder
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.PlacesOver
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_GoodReductionHeight
import Solutions.Source_TripodCyclicBoundOdd

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData

open NumberField

universe u

noncomputable section

variable (C : EllipticCurveData.{u})

/-- The curve's j-invariant as an element of its field of moduli. -/
def jMod : ↥(fieldOfModuli C.F C.E) :=
  ⟨C.E.j, IntermediateField.mem_adjoin_simple_self ℚ C.E.j⟩

theorem mem_VBadOdd_iff_jMod_pole (CA : C.CurveArithmetic)
    (v : FinitePlace ↥(fieldOfModuli C.F C.E)) :
    v ∈ C.VBadOdd ↔ residueChar v ≠ 2 ∧ 1 < v.maximalIdeal.valuation _ C.jMod := by
  have multIff (w : FinitePlace C.F) (hwv : FinitePlace.LiesOver w v) :
      HasMultiplicativeReductionAt C.E w ↔ 1 < v.maximalIdeal.valuation _ C.jMod := by
    have integralIff :
        w.maximalIdeal.valuation C.F C.E.j ≤ 1 ↔
          v.maximalIdeal.valuation _ C.jMod ≤ 1 := by
      change w.maximalIdeal.valuation C.F (algebraMap _ C.F C.jMod) ≤ 1 ↔ _
      exact JoshiTeich.ReferenceIut.valuation_algebraMap_le_one_iff hwv C.jMod
    rw [hasMultiplicativeReductionAt_iff_of_stable C.E w (CA.stable_reduction w),
      integralIff, not_le]
  constructor
  · rintro ⟨hTwo, ⟨w, hwv⟩, hMult⟩
    exact ⟨hTwo, (multIff w hwv).mp (hMult w hwv)⟩
  · rintro ⟨hTwo, hPole⟩
    refine ⟨hTwo, JoshiTeich.ReferenceIut.FinitePlace.exists_liesOver (K := C.F) v, ?_⟩
    exact fun w hwv => (multIff w hwv).mpr hPole

theorem mem_VBadOf_iff_mem_VBadOdd (ℓ : ℕ)
    (v : FinitePlace ↥(fieldOfModuli C.F C.E)) :
    v ∈ C.VBadOf ℓ ↔ v ∈ C.VBadOdd ∧ residueChar v ≠ ℓ := by
  constructor
  · rintro ⟨hTwo, hEll, hOver, hMult⟩
    exact ⟨⟨hTwo, hOver, hMult⟩, hEll⟩
  · rintro ⟨⟨hTwo, hOver, hMult⟩, hEll⟩
    exact ⟨hTwo, hEll, hOver, hMult⟩

variable (E₀ : WeierstrassCurve ↥(fieldOfModuli C.F C.E))

/-- The odd split-multiplicative places of the moduli model in Joshi III, Section 3. -/
def joshiIIIBadModuliSupport : Set (FinitePlace ↥(fieldOfModuli C.F C.E)) :=
  {v | Odd (residueChar v) ∧ JoshiTeich.ReferenceIut.HasSplitMultiplicativeReductionAt E₀ v}

theorem joshiIIIBadModuliSupport_subset_VBadOdd [E₀.IsElliptic]
    (CA : C.CurveArithmetic) (hj : E₀.j = C.jMod) :
    C.joshiIIIBadModuliSupport E₀ ⊆ C.VBadOdd := by
  intro v hv
  rcases hv with ⟨hOdd, ⟨U, hSplit⟩⟩
  apply (C.mem_VBadOdd_iff_jMod_pole CA v).mpr
  constructor
  · intro hTwo
    rw [hTwo] at hOdd
    norm_num at hOdd
  · rw [← hj]
    exact JoshiTeich.ReferenceIut.one_lt_valuation_j_of_mult E₀ v
      ⟨U, hSplit.toHasMultiplicativeReduction⟩

/-- The P7 places outside the paper support are the odd places outside that support
whose residue characteristic differs from the selected prime. -/
theorem VBadOf_diff_joshiIIIBadModuliSupport (ℓ : ℕ) :
    C.VBadOf ℓ \ C.joshiIIIBadModuliSupport E₀ =
      (C.VBadOdd \ C.joshiIIIBadModuliSupport E₀) ∩ {v | residueChar v ≠ ℓ} := by
  ext v
  change (v ∈ C.VBadOf ℓ ∧ v ∉ C.joshiIIIBadModuliSupport E₀) ↔
    (v ∈ C.VBadOdd ∧ v ∉ C.joshiIIIBadModuliSupport E₀) ∧ residueChar v ≠ ℓ
  rw [C.mem_VBadOf_iff_mem_VBadOdd]
  exact ⟨fun ⟨⟨hv, hEll⟩, hPaper⟩ => ⟨⟨hv, hPaper⟩, hEll⟩,
    fun ⟨⟨hv, hPaper⟩, hEll⟩ => ⟨⟨hv, hEll⟩, hPaper⟩⟩

/-- The paper places outside the P7 support lie over the selected prime. -/
theorem joshiIIIBadModuliSupport_diff_VBadOf [E₀.IsElliptic]
    (CA : C.CurveArithmetic) (hj : E₀.j = C.jMod) (ℓ : ℕ) :
    C.joshiIIIBadModuliSupport E₀ \ C.VBadOf ℓ =
      C.joshiIIIBadModuliSupport E₀ ∩ {v | residueChar v = ℓ} := by
  ext v
  change (v ∈ C.joshiIIIBadModuliSupport E₀ ∧ v ∉ C.VBadOf ℓ) ↔
    v ∈ C.joshiIIIBadModuliSupport E₀ ∧ residueChar v = ℓ
  rw [C.mem_VBadOf_iff_mem_VBadOdd]
  constructor
  · rintro ⟨hv, hP7⟩
    refine ⟨hv, Classical.byContradiction fun hEll => ?_⟩
    exact hP7 ⟨C.joshiIIIBadModuliSupport_subset_VBadOdd E₀ CA hj hv, hEll⟩
  · rintro ⟨hv, hEll⟩
    exact ⟨hv, fun hP7 => hP7.2 hEll⟩

end

end AbcAdaptation.Reference.Iut.EllipticCurveData
