import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaAdelicPacketRegion
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFiniteGlobalLowerBound

/-!
source-id: JT-SCENE1-INITIAL-THETA-ADELIC-PACKET-LOG-VOLUME
source: reference Concrete/Container, vol; Cor312/LogVolume, globalVol and
processionVol; Joshi III ss:weighted-vol and th:moccor-Mochizuki-form2.
fidelity: on the actual common rational-place carrier, proves finite support,
then splits the global prime sum and standard procession into their finite
and archimedean contributions. Transfers the proved actual q-pilot lower
bound with its square coefficient and the exact archimedean contribution.
No sign of the full adelic log-volume is assumed; no negative-absolute-value
or paper theta-volume identity is asserted. Original consumer proofs.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaAdelicPacketLogVolume

open IutInitialThetaAdelicPacketRegion
open scoped BigOperators Classical

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

def packetLogVolume (j : ℕ) : RationalPlace → ℝ
  | .finite p => IutInitialThetaFinitePacketLogVolume.packetLogVolume D p j
  | .infinite => IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j

theorem packetLogVolume_eq_zero_of_not_exceptional (j : ℕ) (vQ : RationalPlace)
    (hv : vQ ∉ exceptionalPlaces D) : packetLogVolume D j vQ = 0 := by
  cases vQ with
  | finite p =>
    apply IutInitialThetaFinitePacketLogVolume.packetLogVolume_eq_zero_of_not_bad
    intro hp
    exact hv ((finite_mem_exceptionalPlaces D p).mpr
      ((IutInitialThetaFinitePacketLogVolume.mem_badPrimes D p).mpr hp))
  | infinite => exact False.elim (hv (Finset.mem_insert_self _ _))

theorem packetLogVolume_support_subset (j : ℕ) :
    Function.support (packetLogVolume D j) ⊆ (exceptionalPlaces D : Set RationalPlace) := by
  intro vQ hv
  by_contra h
  exact hv (packetLogVolume_eq_zero_of_not_exceptional D j vQ h)

theorem packetLogVolume_finite_support (j : ℕ) :
    (Function.support (packetLogVolume D j)).Finite :=
  (exceptionalPlaces D).finite_toSet.subset (packetLogVolume_support_subset D j)

def globalLogVolume (j : ℕ) : ℝ := ∑ᶠ vQ, packetLogVolume D j vQ

theorem globalLogVolume_eq_sum (j : ℕ) :
    globalLogVolume D j = ∑ vQ ∈ exceptionalPlaces D, packetLogVolume D j vQ :=
  finsum_eq_sum_of_support_subset _ (packetLogVolume_support_subset D j)

theorem finite_image_logSum (j : ℕ) :
    (∑ vQ ∈ (IutInitialThetaFinitePacketLogVolume.badPrimes D).image RationalPlace.finite,
      packetLogVolume D j vQ) =
      ∑ p ∈ IutInitialThetaFinitePacketLogVolume.badPrimes D,
        IutInitialThetaFinitePacketLogVolume.packetLogVolume D p j := by
  rw [Finset.sum_image]
  · rfl
  · intro p _ q _ h
    exact RationalPlace.finite.inj h

theorem globalLogVolume_eq_finite_add_arch (j : ℕ) :
    globalLogVolume D j = IutInitialThetaFinitePacketLogVolume.globalLogVolume D j +
      IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j := by
  rw [globalLogVolume_eq_sum, exceptionalPlaces, Finset.sum_insert (by simp),
    finite_image_logSum, ← IutInitialThetaFinitePacketLogVolume.globalLogVolume_eq_sum]
  exact add_comm _ _

theorem globalLogVolume_bounds (j : ℕ) :
    IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j -
        ((j ^ 2 : ℕ) : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤ globalLogVolume D j ∧
      globalLogVolume D j ≤ IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j := by
  rw [globalLogVolume_eq_finite_add_arch]
  have hb := IutInitialThetaFiniteGlobalLowerBound.globalLogVolume_bounds D j
  constructor
  · calc
      _ = -((j ^ 2 : ℕ) : ℝ) * JoshiTeich.ReferenceIut.QPilotData.absLogQ
          (IutTorsionQRootSource.iutInitialThetaQPilotData D) +
            IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j := by ring
      _ ≤ _ := add_le_add hb.1 (le_refl _)
  · simpa only [zero_add] using add_le_add hb.2
      (le_refl (IutInitialThetaArchimedeanPacketRegion.packetLogVolume D j))

def processionLogVolume : ℝ :=
  (∑ i : IutInitialThetaFinitePacketRegion.Index D, globalLogVolume D (i.val + 1)) /
    (((D.prime.ℓ - 1) / 2 : ℕ) : ℝ)

theorem processionLogVolume_eq_finite_add_arch :
    processionLogVolume D = IutInitialThetaFinitePacketLogVolume.processionLogVolume D +
      IutInitialThetaArchimedeanPacketRegion.processionLogVolume D := by
  simp only [processionLogVolume, globalLogVolume_eq_finite_add_arch,
    Finset.sum_add_distrib, add_div,
    IutInitialThetaFinitePacketLogVolume.processionLogVolume,
    IutInitialThetaArchimedeanPacketRegion.processionLogVolume]

theorem processionLogVolume_bounds :
    IutInitialThetaArchimedeanPacketRegion.processionLogVolume D -
        IutInitialThetaFiniteGlobalLowerBound.squareAverage D *
          JoshiTeich.ReferenceIut.QPilotData.absLogQ
            (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤ processionLogVolume D ∧
      processionLogVolume D ≤ IutInitialThetaArchimedeanPacketRegion.processionLogVolume D := by
  rw [processionLogVolume_eq_finite_add_arch]
  have hb := IutInitialThetaFiniteGlobalLowerBound.processionLogVolume_bounds D
  constructor
  · calc
      _ = -(IutInitialThetaFiniteGlobalLowerBound.squareAverage D *
          JoshiTeich.ReferenceIut.QPilotData.absLogQ
            (IutTorsionQRootSource.iutInitialThetaQPilotData D)) +
          IutInitialThetaArchimedeanPacketRegion.processionLogVolume D := by ring
      _ ≤ _ := add_le_add hb.1 (le_refl _)
  · simpa only [zero_add] using add_le_add hb.2
      (le_refl (IutInitialThetaArchimedeanPacketRegion.processionLogVolume D))

end
end JoshiTeich.Act1Scene1.IutInitialThetaAdelicPacketLogVolume
