import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Corollary22

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {X : Corollary312VariantData.{u, v} AG TG}

/-- Attach right-hand-side data indexed by the same initial theta data. -/
def Corollary312VariantData.withRHSData (X : Corollary312VariantData.{u, v} AG TG)
    (R : RHSData.{u, v} X.data) : Corollary312VariantData.{u, v} AG TG where
  data := X.data
  qPilot := X.qPilot
  rhsData := R

/-- Use the same arithmetic invariants on the bundle with the new right-hand side. -/
def Theorem110Invariants.withRHSData (inv : Theorem110Invariants X)
    (R : RHSData.{u, v} X.data) : Theorem110Invariants (X.withRHSData R) where
  emod := inv.emod
  one_le_emod := inv.one_le_emod
  emod_le_dmod := inv.emod_le_dmod
  logDtpd := inv.logDtpd
  logDtpd_nonneg := inv.logDtpd_nonneg
  logFtpd := inv.logFtpd
  logFtpd_nonneg := inv.logFtpd_nonneg
  dst := inv.dst
  dst_prime := inv.dst_prime
  logDK := inv.logDK
  logDK_nonneg := inv.logDK_nonneg
  logDK_eq_zero := inv.logDK_eq_zero

/-- Transport the prime condition and the three tower estimates to the new bundle. -/
theorem Theorem110Certificate.withRHSData {inv : Theorem110Invariants X}
    (cert : Theorem110Certificate inv) (R : RHSData.{u, v} X.data) :
    Theorem110Certificate (inv.withRHSData R) where
  seven_le := cert.seven_le
  bad_mem_dst := cert.bad_mem_dst
  step_ii := cert.step_ii
  step_iii := cert.step_iii

/-- Use a theta-pilot family in the same packet, volume, and hull systems. -/
def RHSData.withThetaPilot {D : InitialThetaData AG TG} (R : RHSData.{u, v} D)
    (theta : ∀ i, R.container.AdmissibleRegion i)
    (admissible : ∀ i, R.hull.IsAdmissible (theta i))
    (leShell : ∀ i, theta i ≤ R.container.logShellAdmissible i) : RHSData.{u, v} D :=
  { R with
    thetaPilot := theta
    thetaPilot_hullAdmissible := admissible
    thetaPilot_le_shell := leShell }

/-- The old local containers and volume bounds apply if they contain the new theta-pilot. -/
def Theorem110Invariants.LocalEstimate.withThetaPilot {inv : Theorem110Invariants X}
    (est : inv.LocalEstimate) (theta : ∀ i, X.rhsData.container.AdmissibleRegion i)
    (admissible : ∀ i, X.rhsData.hull.IsAdmissible (theta i))
    (leShell : ∀ i, theta i ≤ X.rhsData.container.logShellAdmissible i)
    (subset_cont : ∀ i vQ, (theta i).region vQ ⊆ est.cont i vQ) :
    (inv.withRHSData (X.rhsData.withThetaPilot theta admissible leShell)).LocalEstimate where
  cont := est.cont
  cont_mem_hullRegions := est.cont_mem_hullRegions
  thetaPilot_subset := subset_cont
  cont_eq_integral := est.cont_eq_integral
  vol_finite := est.vol_finite
  vol_infinite := est.vol_infinite
  packetVol_mono := est.packetVol_mono

/-- Assemble the P7 result for a replacement right-hand side and its local estimate. -/
theorem exists_p7_witness_withRHSData
    {T : Genl.HeightTheory} {K : T.CBS} {d : ℕ} (I : Corollary22Inputs T K d)
    {x : T.Pt T.tripod} {hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d} {ℓ : ℕ}
    {Paper : Corollary312VariantData.{u, v} AG TG → Prop}
    (R : RHSData.{u, v} X.data) (inv : Theorem110Invariants X)
    (cert : Theorem110Certificate inv) (hPaper : Paper (X.withRHSData R))
    (est : Nonempty (inv.withRHSData R).LocalEstimate)
    (hPrime : X.ℓ = ℓ) (hMod : X.dmod ≤ d)
    (hQ : X.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ)
    (hDiff : T.logDiff T.tripod x = inv.logDtpd)
    (hCondLower : inv.logFtpd ≤ T.logCond T.tripod x)
    (hCondUpper : T.logCond T.tripod x ≤ inv.logFtpd + Real.log (2 * ℓ)) :
    ∃ (Y : Corollary312VariantData.{u, v} AG TG) (arith : Theorem110Invariants Y),
      Paper Y ∧ Theorem110Certificate arith ∧ Nonempty arith.LocalEstimate ∧
      Y.ℓ = ℓ ∧ Y.dmod ≤ d ∧ Y.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ ∧
      T.logDiff T.tripod x = arith.logDtpd ∧
      arith.logFtpd ≤ T.logCond T.tripod x ∧
      T.logCond T.tripod x ≤ arith.logFtpd + Real.log (2 * ℓ) :=
  ⟨X.withRHSData R, inv.withRHSData R, hPaper, cert.withRHSData R, est, hPrime, hMod, hQ,
    hDiff, hCondLower, hCondUpper⟩

end AbcAdaptation.Reference.Iut

#print axioms AbcAdaptation.Reference.Iut.Corollary312VariantData.withRHSData
#print axioms AbcAdaptation.Reference.Iut.Theorem110Certificate.withRHSData
#print axioms AbcAdaptation.Reference.Iut.Theorem110Invariants.LocalEstimate.withThetaPilot
#print axioms AbcAdaptation.Reference.Iut.exists_p7_witness_withRHSData
