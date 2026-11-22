import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_LogVolumeBound
import Solutions.Source_ReferenceIutCor312PaperPacketBounds

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {X : Corollary312VariantData.{u, v} AG TG}

/-- An integral packet inside the theta-pilot gives a nonnegative log-volume
for its hull, using the packet measure of the same right-hand side. -/
theorem thetaHull_packetVol_nonneg_of_integral_subset
    {inv : Theorem110Invariants X} (est : inv.LocalEstimate)
    (i : Fin X.rhsData.container.proc.length) (q : RationalPlace)
    (h : (X.rhsData.container.packet i q).integralRegion ⊆
      (X.rhsData.thetaPilot i).region q) :
    0 ≤ X.rhsData.vol.packetVol i q ((X.rhsData.thetaHull i).region q) := by
  let R := X.rhsData
  let H := R.hull.system i q
  have hU : (R.thetaPilot i).region q ∈ H.Admissible :=
    R.thetaPilot_hullAdmissible i q
  have hHull : (R.thetaHull i).region q ∈ H.HullRegions :=
    (H.isLeastHullRegion_hull _ hU).1
  have hle : (R.container.packet i q).integralRegion ⊆ (R.thetaHull i).region q :=
    h.trans (H.subset_hull hU)
  have hvol := est.packetVol_mono i q _ _
    (H.isHullRegion_of_mem _ H.integralRegion_mem) (H.isHullRegion_of_mem _ hHull) hle
  exact (R.vol.packetVol_integral i q).symm ▸ hvol

/-- A prime outside the q-pilot support needs only the integral packet inclusion
for the normalized packet inequality of Corollary 3.12. -/
theorem normalized_packet_bound_of_good_place
    {inv : Theorem110Invariants X} (est : inv.LocalEstimate)
    (capsule : Fin X.lstar ≃ Fin X.rhsData.container.proc.length)
    (j : Fin X.lstar) (p : Nat.Primes)
    (hSupport : ∀ w : X.qPilot.badFinset, residueChar w.1 ≠ (p : ℕ))
    (h : (X.rhsData.container.packet (capsule j) (.finite p)).integralRegion ⊆
      (X.rhsData.thetaPilot (capsule j)).region (.finite p)) :
    (((j.1 : ℝ) + 1) / (X.lstar : ℝ)) ^ 2 * X.signedQLogAt (.finite p) ≤
      X.rhsData.vol.packetVol (capsule j) (.finite p)
        ((X.rhsData.thetaHull (capsule j)).region (.finite p)) := by
  have hlog : X.logQAt p = 0 := by
    unfold Corollary312VariantData.logQAt
    exact Finset.sum_eq_zero fun w hw => (hSupport w (Finset.mem_filter.mp hw).2).elim
  simpa only [Corollary312VariantData.signedQLogAt, hlog, zero_div, neg_zero, mul_zero] using
    thetaHull_packetVol_nonneg_of_integral_subset est (capsule j) (.finite p) h

end AbcAdaptation.Reference.Iut
