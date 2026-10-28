import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDegreeBlockGroupedRegionVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperVossPrimeFiberAccounting

/-!
source-id: JT-SCENE1-INITIAL-THETA-DEGREE-BLOCK-GLOBAL-VOLUME
source: Joshi III `ss:weighted-vol`, `eq:weights` (3522--3557), the actual
finite residue-characteristic decomposition of the section/Voss carrier, and
the proved grouped degree-block root volumes.
fidelity: assembles the actual grouped root volumes over the finite rational
prime support of the concrete section/Voss carrier. It proves positivity and
an exact finite sum formula for the negative logarithm by consuming the local
block identities. This remains an actual finite product and does not identify
it with a paper theta-volume or a paper carrier.
boundary: Scene1/Derived; paper `L'`, mixed-moduli descent, and producer laws
remain open. Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1.DegreeBlockGlobalVolume

open JoshiTeich.Prologue SelectedDegreeBlockVolume DegreeBlockGroupedRegionVolume
open scoped BigOperators Classical
universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

abbrev PrimeSupport := iutInitialThetaSectionVossPrimeSupportType D

theorem primeProof (p : PrimeSupport D) : p.1.Prime := by
  obtain ⟨w, hw⟩ :=
    (iutInitialThetaSectionVossAtPrime_nonempty_iff D p.1).mpr p.2
  exact iutInitialThetaSectionVossAtPrime_prime D p.1 hw

noncomputable def groupedRootVolumeAtPrime (p : PrimeSupport D) : ℝ := by
  let _ : Fact p.1.Prime := ⟨primeProof D p⟩
  exact groupedRegionVolume D p.1 (logRegions D p.1)

def groupedRootVolumeProduct : ℝ :=
  ∏ p : PrimeSupport D, groupedRootVolumeAtPrime D p

theorem groupedRootVolumeAtPrime_eq_relativeRootVolume
    (p : PrimeSupport D) :
    groupedRootVolumeAtPrime D p =
      SelectedThetaTensor.relativeRootVolume D p.1 := by
  let _ : Fact p.1.Prime := ⟨primeProof D p⟩
  exact groupedRegionVolume_logRegions_eq_relativeRootVolume D p.1

theorem groupedRootVolumeProduct_eq_relativeRootVolume_product :
    groupedRootVolumeProduct D =
      ∏ p : PrimeSupport D,
        SelectedThetaTensor.relativeRootVolume D p.1 := by
  unfold groupedRootVolumeProduct
  apply Finset.prod_congr rfl
  intro p hp
  exact groupedRootVolumeAtPrime_eq_relativeRootVolume D p

theorem groupedRootVolumeAtPrime_pos (p : PrimeSupport D) :
    0 < groupedRootVolumeAtPrime D p := by
  let _ : Fact p.1.Prime := ⟨primeProof D p⟩
  exact groupedRegionVolume_logRegions_pos D p.1

theorem groupedRootVolumeProduct_pos : 0 < groupedRootVolumeProduct D := by
  unfold groupedRootVolumeProduct
  exact Finset.prod_pos (fun p _ => groupedRootVolumeAtPrime_pos D p)

theorem groupedRootVolumeAtPrime_negLog_eq_ordp_sum
    (p : PrimeSupport D) :
    -Real.log (groupedRootVolumeAtPrime D p) =
      ∑ i : Index D p.1,
        (Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p.1 i) : ℝ) *
          Arithmetic.ordp (SelectedThetaTensor.sourceAt D p.1 i).1
            ((iutInitialThetaOddSupportTorsionQRootSource D).qroot
              (SelectedThetaTensor.sourceAt D p.1 i)) * Real.log p.1 := by
  let _ : Fact p.1.Prime := ⟨primeProof D p⟩
  exact groupedRegionVolume_logRegions_negLog_eq_ordp_sum D p.1

theorem groupedRootVolumeProduct_negLog_eq_prime_sum :
    -Real.log (groupedRootVolumeProduct D) =
      ∑ p : PrimeSupport D,
        ∑ i : Index D p.1,
          (Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p.1 i) : ℝ) *
            Arithmetic.ordp (SelectedThetaTensor.sourceAt D p.1 i).1
              ((iutInitialThetaOddSupportTorsionQRootSource D).qroot
                (SelectedThetaTensor.sourceAt D p.1 i)) * Real.log p.1 := by
  rw [groupedRootVolumeProduct,
    Real.log_prod (fun p _ => (groupedRootVolumeAtPrime_pos D p).ne'),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  exact groupedRootVolumeAtPrime_negLog_eq_ordp_sum D p

end
end JoshiTeich.Act1Scene1.DegreeBlockGlobalVolume
