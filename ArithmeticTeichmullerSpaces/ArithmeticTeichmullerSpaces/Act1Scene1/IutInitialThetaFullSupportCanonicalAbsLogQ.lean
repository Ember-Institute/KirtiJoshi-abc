import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaSelectedBaseSupportCoverageAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootAccounting

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Arithmetic
open NumberField
open scoped BigOperators Classical NumberField

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-FULL-SUPPORT-CANONICAL-ABSLOGQ
source: the full-support weighted logarithmic accounting in
`IutInitialThetaSelectedBaseSupportCoverageAccounting.lean`, the actual
`InitialThetaData` q-root accounting in `IutInitialThetaQRootAccounting.lean`,
and the reference `QPilotData.absLogQ` fibre decomposition ported from `iut`.
fidelity: under an explicit equality between the complete odd multiplicative
support and `badPlacesOver(VBad)`, transports the full-support weighted log sum
to the reference q-pilot `absLogQ`. The proof compares both q-root sources
through their common base q-order accounting and does not identify their
chosen q-root functions pointwise.
boundary: Scene1/Derived
-/

theorem iutInitialThetaOddSupportWeighted_logSum_eq_reference_absLogQ_of_support_eq
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (hSupport : IutOddMultiplicativeSupport D =
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    let B := iutInitialThetaOddSupportBaseQPilotSource D
    ∑ p ∈ B.badFinset.image Arithmetic.residueChar,
        Real.log p * IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  classical
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let Q := IutTorsionQRootSource.iutInitialThetaQPilotData D
  have hBPlaces : (↑B.badFinset : Set (NumberField.FinitePlace D.F)) =
      IutOddMultiplicativeSupport D := B.badFinset_spec
  have hBad : (↑B.badFinset : Set (NumberField.FinitePlace D.F)) =
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
    hBPlaces.trans hSupport
  have hQFin : Q.badFinset = B.badFinset := by
    apply Finset.ext
    intro w
    have hQ := Set.ext_iff.mp Q.badFinset_spec w
    have hB := Set.ext_iff.mp B.badFinset_spec w
    constructor
    · intro hw
      have hwBad : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
        Q.mem_bad hw
      have hwFull : w ∈ IutOddMultiplicativeSupport D :=
        (Set.ext_iff.mp hSupport w).mpr hwBad
      exact Finset.mem_coe.mp (hB.mpr hwFull)
    · intro hw
      have hwFull : w ∈ IutOddMultiplicativeSupport D :=
        hB.mp (Finset.mem_coe.mpr hw)
      have hwBad : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
        (Set.ext_iff.mp hSupport w).mp hwFull
      exact Finset.mem_coe.mp (hQ.mpr hwBad)
  have hCanonicalFiber (p : ℕ) :
      IutTorsionQRootSource.canonical_qroot_weighted_fiber_of_initialThetaData D p =
        ∑ w ∈ B.badFinset.attach.filter
            (fun w => Arithmetic.residueChar w.1 = p),
          Arithmetic.qPilotWeight w.1 * (B.qOrder w : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := by
    letI : Finite {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p} := Arithmetic.fiber_finite p
    letI : Fintype {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p} := Fintype.ofFinite _
    have hCanon :=
      IutTorsionQRootSource.canonical_qroot_weighted_sum_of_initialThetaData D p
        B.badFinset hBad
    calc
      IutTorsionQRootSource.canonical_qroot_weighted_fiber_of_initialThetaData D p =
          ∑ w ∈ B.badFinset.filter
            (fun w => Arithmetic.residueChar w = p),
            (Arithmetic.inertDeg w : ℝ) / Module.finrank ℚ D.F *
              (if hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad then
                (D.prime.qOrder w hw : ℝ) / (2 * (D.prime.ℓ : ℝ))
              else 0) := by
        simpa [IutTorsionQRootSource.canonical_qroot_weighted_fiber_of_initialThetaData, B]
          using hCanon
      _ = ∑ w ∈ B.badFinset.attach.filter
            (fun w => Arithmetic.residueChar w.1 = p),
            Arithmetic.qPilotWeight w.1 * (B.qOrder w : ℝ) /
              (2 * (D.prime.ℓ : ℝ)) := by
        rw [Finset.sum_filter]
        rw [← Finset.sum_attach]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro w hw
        have hwB : w.1 ∈ B.badFinset := w.2
        have hwFull : w.1 ∈ IutOddMultiplicativeSupport D :=
          (Set.ext_iff.mp B.badFinset_spec w.1).mp (Finset.mem_coe.mpr hwB)
        have hwBad : w.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
          (Set.ext_iff.mp hSupport w.1).mp hwFull
        have hq := iutInitialThetaOddSupportBaseQPilotSource_qOrder_eq_admissiblePrime
          D ⟨w.1, hwB⟩ hwBad
        have hqPilot : Arithmetic.qPilotWeight w.1 =
            (Arithmetic.inertDeg w.1 : ℝ) / Module.finrank ℚ D.F := rfl
        rw [hqPilot, dif_pos hwBad, hq]
        ring
  have hFullFiber (p : ℕ) :
      IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p =
        ∑ w ∈ B.badFinset.attach.filter
            (fun w => Arithmetic.residueChar w.1 = p),
          Arithmetic.qPilotWeight w.1 * (B.qOrder w : ℝ) /
            (2 * (D.prime.ℓ : ℝ)) := by
    simpa [B] using
      (IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber_eq_baseQOrder D p)
  have hFibers (p : ℕ) :
      IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p =
        IutTorsionQRootSource.canonical_qroot_weighted_fiber_of_initialThetaData D p := by
    rw [hFullFiber, hCanonicalFiber]
  have hLog :
      ∑ p ∈ Q.badFinset.image Arithmetic.residueChar,
        Real.log p *
          IutTorsionQRootSource.canonical_qroot_weighted_fiber_of_initialThetaData D p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ Q := by
    simpa [Q] using IutTorsionQRootSource.canonical_qroot_log_sum_eq_iut_absLogQ D
  rw [hQFin] at hLog
  change ∑ p ∈ B.badFinset.image Arithmetic.residueChar,
      Real.log p * IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p =
    JoshiTeich.ReferenceIut.QPilotData.absLogQ Q
  calc
    ∑ p ∈ B.badFinset.image Arithmetic.residueChar,
        Real.log p * IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p =
        ∑ p ∈ B.badFinset.image Arithmetic.residueChar,
          Real.log p *
            IutTorsionQRootSource.canonical_qroot_weighted_fiber_of_initialThetaData D p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hFibers]
    _ = JoshiTeich.ReferenceIut.QPilotData.absLogQ Q := by
      simpa [Q, B] using hLog

end

end JoshiTeich.Act1Scene1
