import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalActualHullVolumeSign

/-!
source-id: JT-SCENE1-CANONICAL-ACTUAL-HULL-STRICT-VOLUME
source: the actual VBad nonemptiness, representative coefficient bounds,
positive paper terms, and canonical generated-hull volume formula; Joshi III
1028--1055 and 3495--3557.
fidelity: proves strict positivity of the internal coefficient-weighted paper
sum and transfers it to `thetaVolume < 1` and `log thetaVolume < 0` for the
canonical actual-hull target.  It does not identify this internal sum with a
paper theta locus or supply a global producer.
boundary: Scene1/Derived; paper normalization and G1--G4 identities remain open.
-/

namespace JoshiTeich.Act1Scene1.CanonicalActualHull.StrictVolume

open JoshiTeich.Prologue
open scoped BigOperators Classical
universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem coefficientWeightedPaperSum_pos :
    0 < ∑ v : iutInitialThetaVBadModuliFinset D,
      iutInitialThetaRepresentativeCoefficient D
          (iutInitialThetaVBadModuliAt D v) *
        VBadSelectedPaper.paperTerm D v := by
  have hterm (v : iutInitialThetaVBadModuliFinset D) :
      0 < iutInitialThetaRepresentativeCoefficient D
          (iutInitialThetaVBadModuliAt D v) *
        VBadSelectedPaper.paperTerm D v :=
    mul_pos
      (iutInitialThetaRepresentativeCoefficient_mem_Ioc D
        (iutInitialThetaVBadModuliAt D v)).1
      (VBadSelectedPaper.paperTerm_pos D v)
  obtain ⟨v, hv⟩ := D.global.bad_nonempty
  let v₀ : iutInitialThetaVBadModuliFinset D :=
    ⟨v, (mem_iutInitialThetaVBadModuliFinset_iff D v).mpr hv⟩
  have hne : (Finset.univ : Finset (iutInitialThetaVBadModuliFinset D)).Nonempty :=
    ⟨v₀, Finset.mem_univ _⟩
  exact Finset.sum_pos (fun w _ => hterm w) hne

variable {O : Type u} [CommRing O]
variable (p : ℕ) [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable (theta : ThetaPilotData D.F)
variable (route : CanonicalActualHull.PositivePacket D → theta.index)
variable (thetaBase : theta.index)
variable (heightData : Arithmetic.HeightData D.F)
variable (ramification : Arithmetic.RamificationProfile D.F)
variable (X : CanonicalActualHull.AnalyticInput (O := O) p D theta route thetaBase
  heightData ramification)

local instance selectedPrime (v : iutInitialThetaVBadModuliFinset D) :
    Fact (Arithmetic.residueChar v.1).Prime :=
  ⟨Arithmetic.residueChar_prime v.1⟩

abbrev Target := CanonicalActualHull.data p D theta route thetaBase heightData ramification X

theorem thetaVolume_lt_one :
    (Target D p theta route thetaBase heightData ramification X).thetaVolume < 1 := by
  rw [CanonicalActualHull.data_thetaVolume_eq p D theta route thetaBase heightData ramification X,
    CanonicalActualHull.hullVolume_eq_exp_neg_coefficientWeightedPaperSum D]
  rw [Real.exp_lt_one_iff]
  rw [neg_mul]
  apply neg_lt_zero.mpr
  exact mul_pos
    (by exact_mod_cast (CanonicalActualHull.length_pos D))
    (coefficientWeightedPaperSum_pos D)

theorem log_thetaVolume_neg :
    Real.log (Target D p theta route thetaBase heightData ramification X).thetaVolume < 0 :=
  Real.log_neg
    (CanonicalActualHull.SideConditions.sideConditions p D theta route thetaBase
      heightData ramification X).thetaVolume_pos
    (thetaVolume_lt_one D p theta route thetaBase heightData ramification X)

end
end JoshiTeich.Act1Scene1.CanonicalActualHull.StrictVolume
