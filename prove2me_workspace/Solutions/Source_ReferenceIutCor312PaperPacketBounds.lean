import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_LocalHeightDataAssembly
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Invariants
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open scoped BigOperators

universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

namespace Corollary312VariantData

variable (X : Corollary312VariantData.{u, v} AG TG)

private noncomputable def qPilotPlace (w : X.qPilot.badFinset) : RationalPlace :=
  .finite ⟨residueChar w.1, residueChar_prime (k := X.data.F) w.1⟩

/-- The signed q-pilot contribution at a rational place. Its finite terms are
grouped by residue characteristic and its infinite term is zero. -/
noncomputable def signedQLogAt : RationalPlace → ℝ
  | .finite p => -(X.logQAt p.val / (2 * (X.ℓ : ℝ)))
  | .infinite => 0

private theorem signedQLogAt_eq_sum (q : RationalPlace) :
    X.signedQLogAt q =
      ∑ w ∈ X.qPilot.badFinset.attach.filter (fun w => X.qPilotPlace w = q),
        -(X.qPilot.weight w.1 * (X.data.prime.qOrder w.1 (X.qPilot.mem_bad w.2) : ℝ) *
          Real.log (residueChar w.1) / (2 * (X.ℓ : ℝ))) := by
  cases q with
  | infinite =>
    simp [signedQLogAt, qPilotPlace]
  | finite p =>
    have hfilter :
        (X.qPilot.badFinset.attach.filter (fun w => X.qPilotPlace w = .finite p)) =
        X.qPilot.badFinset.attach.filter (fun w => residueChar w.1 = p.val) := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hw, hplace⟩
        exact ⟨hw, congrArg RationalPlace.residueChar hplace⟩
      · rintro ⟨hw, hp⟩
        exact ⟨hw, congrArg RationalPlace.finite (Subtype.ext hp)⟩
    rw [hfilter, signedQLogAt, logQAt, Finset.sum_neg_distrib, Finset.sum_div]

private theorem signedQLogAt_support_subset
    (s : Finset RationalPlace)
    (hs : ∀ w : X.qPilot.badFinset, X.qPilotPlace w ∈ s) :
    Function.support X.signedQLogAt ⊆ (s : Set RationalPlace) := by
  intro q hq
  by_contra hmiss
  apply hq
  rw [X.signedQLogAt_eq_sum]
  exact Finset.sum_eq_zero fun w hw =>
    (hmiss ((Finset.mem_filter.mp hw).2 ▸ hs w)).elim

private theorem signedQLogAt_support :
    (Function.support X.signedQLogAt).Finite := by
  classical
  exact (X.qPilot.badFinset.attach.image X.qPilotPlace).finite_toSet.subset
    (X.signedQLogAt_support_subset _ fun w =>
      Finset.mem_image_of_mem X.qPilotPlace (Finset.mem_attach _ w))

/-- Summing the signed local contributions recovers the original q-pilot. -/
theorem finsum_signedQLogAt : (∑ᶠ q, X.signedQLogAt q) = X.qPilot.lhs := by
  classical
  let s := X.qPilot.badFinset.attach.image X.qPilotPlace
  have hsupport := X.signedQLogAt_support_subset s fun w =>
    Finset.mem_image_of_mem X.qPilotPlace (Finset.mem_attach _ w)
  rw [finsum_eq_sum_of_support_subset X.signedQLogAt hsupport]
  simp_rw [signedQLogAt_eq_sum]
  rw [Finset.sum_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem X.qPilotPlace hw),
    Finset.sum_neg_distrib, ← Finset.sum_div]
  rfl

end Corollary312VariantData

private theorem packetVol_support {D : InitialThetaData AG TG} (R : RHSData.{u, v} D)
    (i : Fin R.container.proc.length) :
    (Function.support fun q => R.vol.packetVol i q ((R.thetaHull i).region q)).Finite := by
  refine (R.thetaHull i).finiteSupport.subset ?_
  intro q hn h
  apply hn
  change R.vol.packetVol i q ((R.thetaHull i).region q) = 0
  rw [h, R.vol.packetVol_integral]

/-- The packet inequalities for the paper hull imply the reference comparison.
The index identification retains every capsule. Outside the finite q-pilot
support, the packet inequality requires nonnegative log-volume. -/
theorem corollary312Variant_of_normalized_packet_bounds
    (X : Corollary312VariantData.{u, v} AG TG)
    (capsule : Fin X.lstar ≃ Fin X.rhsData.container.proc.length)
    (hpacket : ∀ (j : Fin X.lstar) q,
      (((j.1 : ℝ) + 1) / (X.lstar : ℝ)) ^ 2 * X.signedQLogAt q ≤
        X.rhsData.vol.packetVol (capsule j) q ((X.rhsData.thetaHull (capsule j)).region q)) :
    Corollary312Variant X := by
  have hm : 0 < X.lstar := by
    have h := X.data.prime.five_le
    change 5 ≤ X.ℓ at h
    change 0 < (X.ℓ - 1) / 2
    omega
  have hmR : (0 : ℝ) < X.lstar := by exact_mod_cast hm
  have hq : X.qPilot.lhs ≤ 0 := by
    apply neg_nonpos.mpr
    apply div_nonneg _ (by positivity)
    unfold QPilotData.logQ
    refine Finset.sum_nonneg fun w _ => ?_
    exact mul_nonneg (mul_nonneg (X.qPilot.weight_pos w.1 w.2).le (Nat.cast_nonneg _))
      (Real.log_nonneg (by exact_mod_cast (residueChar_prime w.1).one_lt.le))
  have hlength : X.lstar = X.rhsData.container.proc.length := by
    simpa using Fintype.card_congr capsule
  have hglobal (j : Fin X.lstar) :
      X.qPilot.lhs ≤ X.rhsData.vol.globalVol (X.rhsData.thetaHull (capsule j)) := by
    let c : ℝ := (((j.1 : ℝ) + 1) / (X.lstar : ℝ)) ^ 2
    have hj : (j.1 : ℝ) + 1 ≤ X.lstar := by exact_mod_cast Nat.succ_le_of_lt j.2
    have hc : c ≤ 1 := by
      have hd := (div_le_one hmR).mpr hj
      exact pow_le_one₀ (by positivity) hd
    have hsupport : (Function.support fun q => c * X.signedQLogAt q).Finite := by
      refine X.signedQLogAt_support.subset ?_
      intro q hq hz
      exact hq (by simp [hz])
    calc
      X.qPilot.lhs ≤ c * X.qPilot.lhs := by
        simpa only [one_mul] using mul_le_mul_of_nonpos_right hc hq
      _ = ∑ᶠ q, c * X.signedQLogAt q := by
        rw [← mul_finsum, X.finsum_signedQLogAt]
      _ ≤ X.rhsData.vol.globalVol (X.rhsData.thetaHull (capsule j)) :=
        finsum_le_finsum' hsupport
          (packetVol_support X.rhsData (capsule j)) (hpacket j)
  change X.qPilot.lhs ≤ X.rhsData.rhs
  unfold RHSData.rhs LogVolumeData.processionVol
  have hden : (0 : ℝ) < X.rhsData.container.proc.length := hlength ▸ hmR
  apply (le_div_iff₀ hden).mpr
  calc
    X.qPilot.lhs * (X.rhsData.container.proc.length : ℝ) = ∑ _j : Fin X.lstar, X.qPilot.lhs := by
      simp [← hlength, mul_comm]
    _ ≤ ∑ j : Fin X.lstar, X.rhsData.vol.globalVol (X.rhsData.thetaHull (capsule j)) :=
      Finset.sum_le_sum fun j _ => hglobal j
    _ = _ := Equiv.sum_comp capsule
      (fun i => X.rhsData.vol.globalVol (X.rhsData.thetaHull i))

end AbcAdaptation.Reference.Iut
