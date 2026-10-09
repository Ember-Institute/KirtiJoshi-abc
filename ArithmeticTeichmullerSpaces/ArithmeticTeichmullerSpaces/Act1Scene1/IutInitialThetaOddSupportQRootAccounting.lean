import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOddSupportQRoot
import ArithmeticTeichmullerSpaces.Act1Scene1.IutQRootAccounting

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Arithmetic
open WithZero
open scoped BigOperators Classical NumberField Valued

universe u

noncomputable section

/-!
source-id: IUT-COR312-ODD-SUPPORT-QROOT-ACCOUNTING
source: `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean`,
`ThetaLocalData.sum_weight_ordp_qroot`; `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean`,
`sum_localDeg_liesOver` and the completion valuation normalization.
fidelity: specializes the finite-place weighted q-root identity to the real
`InitialThetaData` Tate family on its complete odd multiplicative support. The
q-order is derived from the completion valuation of the actual base Tate
parameter. This is accounting on that full support; it does not identify the
paper's selected `L'` representatives, `underline V^oss`, or its unweighted sum.
boundary: Scene1/Derived
-/

namespace IutTorsionQRootSource

/-- The q-root contribution over all torsion-field places of residue
characteristic `p`, with the actual odd-support carrier. -/
noncomputable def iutInitialThetaOddSupportWeightedFiber
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) : ℝ := by
  letI : Finite {v : NumberField.FinitePlace ↥D.prime.torsionField //
    Arithmetic.residueChar v = p} := Arithmetic.fiber_finite p
  letI : Fintype {v : NumberField.FinitePlace ↥D.prime.torsionField //
    Arithmetic.residueChar v = p} := Fintype.ofFinite _
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  exact ∑ v : {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p},
    Arithmetic.placeWeight v.1 *
      (if hv : v.1 ∈ R.badFinset then
        Arithmetic.ordp v.1 (R.qroot ⟨v.1, hv⟩)
      else 0)

/-- On the complete odd multiplicative support, torsion q-root valuation sums
to the residue-degree weighted base q-order sum at each rational prime. -/
theorem iutInitialThetaOddSupportWeightedFiber_eq_baseQOrder
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) :
    iutInitialThetaOddSupportWeightedFiber D p =
      ∑ w ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.attach.filter
          (fun w => Arithmetic.residueChar w.1 = p),
        Arithmetic.qPilotWeight w.1 *
          ((iutInitialThetaOddSupportBaseQPilotSource D).qOrder w : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := by
  classical
  letI : Finite {v : NumberField.FinitePlace ↥D.prime.torsionField //
    Arithmetic.residueChar v = p} := Arithmetic.fiber_finite p
  letI : Fintype {v : NumberField.FinitePlace ↥D.prime.torsionField //
    Arithmetic.residueChar v = p} := Fintype.ofFinite _
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let c : NumberField.FinitePlace D.F → ℝ := fun w =>
    if hw : w ∈ B.badPlaces then
      (B.qOrder ⟨w, (Set.ext_iff.mp B.badFinset_spec w).mpr hw⟩ : ℝ) /
        (2 * (D.prime.ℓ : ℝ))
    else 0
  have hc : ∀ w : B.badFinset,
      c w.1 = (B.qOrder w : ℝ) / (2 * (D.prime.ℓ : ℝ)) := by
    intro w
    simp [c, B.mem_badPlaces]
  have hsum := IutTorsionQRootSource.canonical_qroot_weighted_sum
    (B := B) p B.badFinset B.badFinset_spec c hc R.qroot R.qroot_pow_eq
    (fun w => iutCompletionQOrder_valued w.1 (B.tateParameter w)
      (B.tateParameter_ne_zero w) (B.tateParameter_norm_lt_one w))
    (by have h := D.prime.five_le; omega)
  have hrootCarrier : R.badFinset =
      iutBadPlacesOverFinset (k := D.F) (K := ↥D.prime.torsionField)
        B.badPlaces B.badPlaces_finite := by
    rfl
  have hsum' :
      (∑ v : {v : NumberField.FinitePlace ↥D.prime.torsionField //
          Arithmetic.residueChar v = p},
        Arithmetic.placeWeight v.1 *
          (if hv : v.1 ∈ R.badFinset then
            Arithmetic.ordp v.1 (R.qroot ⟨v.1, hv⟩) else 0)) =
        ∑ w ∈ B.badFinset.filter (fun w => Arithmetic.residueChar w = p),
          (Arithmetic.inertDeg w : ℝ) / Module.finrank ℚ D.F * c w := by
    exact hsum
  change (∑ v : {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p},
    Arithmetic.placeWeight v.1 *
      (if hv : v.1 ∈ R.badFinset then
        Arithmetic.ordp v.1 (R.qroot ⟨v.1, hv⟩)
      else 0)) = _
  rw [hsum']
  unfold B
  calc
    _ = ∑ w ∈ (iutInitialThetaOddSupportBaseQPilotSource D).badFinset.attach.filter
          (fun w => Arithmetic.residueChar w.1 = p),
        (Arithmetic.inertDeg w.1 : ℝ) /
            Module.finrank ℚ D.F * c w.1 := by
      rw [Finset.sum_filter]
      rw [← Finset.sum_attach]
      rw [Finset.sum_filter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      have hc' := hc w
      rw [hc']
      unfold Arithmetic.qPilotWeight
      ring

end IutTorsionQRootSource

end

end JoshiTeich.Act1Scene1
