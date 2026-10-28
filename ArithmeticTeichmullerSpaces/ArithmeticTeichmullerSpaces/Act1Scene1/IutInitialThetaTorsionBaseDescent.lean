import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaGaloisFiberMass

/-!
source-id: JT-SCENE1-INITIAL-THETA-TORSION-BASE-DESCENT
source: Joshi III `ss:weighted-vol`, `eq:weights`; actual complete over-place
fibres, their degree sum and mass formula, and corrected q-root norm invariance.
fidelity: proves that every base source place has a torsion source place,
constructs a section and a finite sigma equivalence, and regroups the entire
source's mass and corrected q-root log sum with the computed ramification
coefficient. No section law or mass-one law is supplied by the caller.
boundary: Scene1/Derived; fixed Initial Theta data and F-place carrier.
Paper representatives, different untilts and theta-volume remain separate.
Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue NumberField
open scoped BigOperators
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem iutInitialThetaTorsionBaseFiber_nonempty
    (b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
    (iutInitialThetaTorsionBaseFiber D b).Nonempty := by
  let : Module.Finite D.F ↥D.prime.torsionField :=
    Module.Finite.of_restrictScalars_finite ℚ D.F ↥D.prime.torsionField
  have hpos : 0 < Module.finrank D.F ↥D.prime.torsionField * Arithmetic.localDeg b.1 :=
    Nat.mul_pos Module.finrank_pos (Arithmetic.localDeg_pos b.1)
  have hsum := Arithmetic.sum_localDeg_liesOver b.1 (iutInitialThetaTorsionBaseFiber D b)
    (mem_iutInitialThetaTorsionBaseFiber_iff D b)
  by_contra hnone
  rw [Finset.not_nonempty_iff_eq_empty.mp hnone, Finset.sum_empty] at hsum
  exact (Nat.ne_of_gt hpos) hsum.symm

theorem iutInitialThetaTorsionSource_basePlace_surjective :
    Function.Surjective (iutInitialThetaOddSupportTorsionQRootSource D).basePlace := by
  intro b
  obtain ⟨v, hv⟩ := iutInitialThetaTorsionBaseFiber_nonempty D b
  exact ⟨iutInitialThetaTorsionBaseFiberSource D b ⟨v, hv⟩,
    iutInitialThetaTorsionBaseFiberSource_basePlace D b ⟨v, hv⟩⟩

def iutInitialThetaTorsionBaseSection
    (b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
    (iutInitialThetaOddSupportTorsionQRootSource D).badFinset :=
  (iutInitialThetaTorsionSource_basePlace_surjective D b).choose

theorem iutInitialThetaTorsionBaseSection_basePlace
    (b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset) :
    (iutInitialThetaOddSupportTorsionQRootSource D).basePlace
      (iutInitialThetaTorsionBaseSection D b) = b :=
  (iutInitialThetaTorsionSource_basePlace_surjective D b).choose_spec

def iutInitialThetaTorsionSourceBaseFiberSigmaEquiv :
    (iutInitialThetaOddSupportTorsionQRootSource D).badFinset ≃
      Σ b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset,
        iutInitialThetaTorsionBaseFiber D b := by
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  refine
    { toFun := fun s => ⟨R.basePlace s, ⟨s.1,
        (mem_iutInitialThetaTorsionBaseFiber_iff D (R.basePlace s) s.1).mpr (R.liesOver s)⟩⟩
      invFun := fun x => iutInitialThetaTorsionBaseFiberSource D x.1 x.2
      left_inv := fun s => Subtype.ext rfl
      right_inv := ?_ }
  rintro ⟨b, v⟩
  have hb := iutInitialThetaTorsionBaseFiberSource_basePlace D b v
  apply Sigma.ext hb
  have hpred (x : FinitePlace ↥D.prime.torsionField) :
      x ∈ iutInitialThetaTorsionBaseFiber D
        (R.basePlace (iutInitialThetaTorsionBaseFiberSource D b v)) ↔
        x ∈ iutInitialThetaTorsionBaseFiber D b := by rw [hb]
  exact (Subtype.heq_iff_coe_eq hpred).mpr rfl

theorem iutInitialThetaTorsionSource_sum_baseFibers
    (f : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset → ℝ) :
    (∑ s, f s) =
      ∑ b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset,
        ∑ v : iutInitialThetaTorsionBaseFiber D b,
          f (iutInitialThetaTorsionBaseFiberSource D b v) := by
  rw [← Fintype.sum_sigma' (fun b v => f (iutInitialThetaTorsionBaseFiberSource D b v))]
  exact ((iutInitialThetaTorsionSourceBaseFiberSigmaEquiv D).symm.sum_comp f).symm

theorem iutInitialThetaTorsionSource_mass_eq_baseSectionSum :
    (∑ s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
      Arithmetic.qPilotWeight s.1) =
      ∑ b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset,
        Arithmetic.qPilotWeight b.1 /
          (Arithmetic.relRamIdx (iutInitialThetaTorsionBaseSection D b).1 b.1 : ℝ) := by
  rw [iutInitialThetaTorsionSource_sum_baseFibers D (fun s => Arithmetic.qPilotWeight s.1)]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = ∑ v ∈ iutInitialThetaTorsionBaseFiber D b, Arithmetic.qPilotWeight v :=
      Finset.sum_coe_sort _ _
    _ = _ := by
      simpa only [iutInitialThetaTorsionBaseSection_basePlace] using
        iutInitialThetaTorsionBaseFiber_mass_eq_base_div_relativeRamIdx D
          (iutInitialThetaTorsionBaseSection D b)

theorem iutInitialThetaTorsionSource_weightedPaperLogSum_eq_baseSectionSum :
    (∑ s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset,
      Arithmetic.qPilotWeight s.1 * (-Real.log (actualPaperRootNorm D s))) =
      ∑ b : (iutInitialThetaOddSupportBaseQPilotSource D).badFinset,
        (Arithmetic.qPilotWeight b.1 /
          (Arithmetic.relRamIdx (iutInitialThetaTorsionBaseSection D b).1 b.1 : ℝ)) *
          (-Real.log (actualPaperRootNorm D (iutInitialThetaTorsionBaseSection D b))) := by
  rw [iutInitialThetaTorsionSource_sum_baseFibers D
    (fun s => Arithmetic.qPilotWeight s.1 * (-Real.log (actualPaperRootNorm D s)))]
  apply Finset.sum_congr rfl
  intro b _
  let R := iutInitialThetaOddSupportTorsionQRootSource D
  let s := iutInitialThetaTorsionBaseSection D b
  have hsbase : R.basePlace s = b :=
    iutInitialThetaTorsionBaseSection_basePlace D b
  have hterm (v : iutInitialThetaTorsionBaseFiber D b) :
      actualPaperRootNorm D (iutInitialThetaTorsionBaseFiberSource D b v) =
        actualPaperRootNorm D s := by
    have hsrc : R.basePlace (iutInitialThetaTorsionBaseFiberSource D b v) = b :=
      iutInitialThetaTorsionBaseFiberSource_basePlace D b v
    have hbase : R.basePlace (iutInitialThetaTorsionBaseFiberSource D b v) = R.basePlace s := by
      rw [hsrc, hsbase]
    exact actualPaperRootNorm_eq_of_same_basePlace D
      (iutInitialThetaTorsionBaseFiberSource D b v) s hbase
  have hmass :
      (∑ v : iutInitialThetaTorsionBaseFiber D b, Arithmetic.qPilotWeight v.1) =
        Arithmetic.qPilotWeight b.1 /
          (Arithmetic.relRamIdx s.1 b.1 : ℝ) := by
    calc
      _ = ∑ v ∈ iutInitialThetaTorsionBaseFiber D b, Arithmetic.qPilotWeight v :=
        Finset.sum_coe_sort _ _
      _ = _ := LocalCompletion.qPilotWeight_sum_eq_base_div_relativeRamIdx b.1
        (iutInitialThetaTorsionBaseFiber D b)
        (mem_iutInitialThetaTorsionBaseFiber_iff D b) s.1
        ((mem_iutInitialThetaTorsionBaseFiber_iff D b s.1).mpr
          (by simpa [hsbase] using R.liesOver s))
  calc
    _ = (∑ v : iutInitialThetaTorsionBaseFiber D b, Arithmetic.qPilotWeight v.1) *
        (-Real.log (actualPaperRootNorm D s)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun v _ => by
        rw [hterm v]
        rfl
    _ = _ := by rw [hmass]

end
end JoshiTeich.Act1Scene1
