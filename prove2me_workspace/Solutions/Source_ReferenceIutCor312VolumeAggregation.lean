import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Invariants
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Solutions.Source_ReferenceIutConcreteThetaRegion
import Theorems.Thm_AbcAdaptation_Reference_Iut_sum_affine_quadratic

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open scoped BigOperators

universe u v

private theorem finsum_rationalPlace_eq (volume : RationalPlace → ℝ)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime) (finiteVolume : ℕ → ℝ)
    (hfinite : ∀ p : Nat.Primes, volume (.finite p) = finiteVolume p)
    (hzero : ∀ p : Nat.Primes, (p : ℕ) ∉ primes → finiteVolume p = 0) :
    (∑ᶠ q, volume q) = volume .infinite + ∑ p ∈ primes, finiteVolume p := by
  let finiteIndex : {p : ℕ // p ∈ primes} ↪ RationalPlace :=
    ⟨fun p => .finite ⟨p.1, hprime p.1 p.2⟩, fun _ _ h =>
      Subtype.ext (congrArg (fun p : Nat.Primes => p.1) (RationalPlace.finite.inj h))⟩
  let finitePlaces := primes.attach.map finiteIndex
  have hinfinite : RationalPlace.infinite ∉ finitePlaces := by
    intro h
    change RationalPlace.infinite ∈ primes.attach.map finiteIndex at h
    obtain ⟨p, _, hp⟩ := Finset.mem_map.mp h
    change RationalPlace.finite ⟨p.1, hprime p.1 p.2⟩ = .infinite at hp
    cases hp
  have hsupport : Function.support volume ⊆
      (↑(insert RationalPlace.infinite finitePlaces) : Set RationalPlace) := by
    intro q hq
    change volume q ≠ 0 at hq
    change q ∈ insert RationalPlace.infinite finitePlaces
    cases q with
    | infinite => exact Finset.mem_insert_self _ _
    | finite p =>
        have hp : (p : ℕ) ∈ primes := by
          by_contra hnot
          exact hq ((hfinite p).trans (hzero p hnot))
        apply Finset.mem_insert_of_mem
        change RationalPlace.finite p ∈ primes.attach.map finiteIndex
        exact Finset.mem_map.mpr ⟨⟨p.1, hp⟩, Finset.mem_attach _ _,
          congrArg RationalPlace.finite (Subtype.ext rfl)⟩
  rw [finsum_eq_sum_of_support_subset volume hsupport, Finset.sum_insert hinfinite]
  change volume .infinite + (∑ p ∈ primes.attach.map finiteIndex, volume p) = _
  rw [Finset.sum_map, ← Finset.sum_attach primes finiteVolume]
  exact congrArg (fun s : ℝ => volume .infinite + s) <|
    Finset.sum_congr rfl fun p _ => hfinite ⟨p.1, hprime p.1 p.2⟩

section QPilot

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (X : Corollary312VariantData.{u, v} AG TG) (primes : Finset ℕ)
variable (hbad : ∀ w ∈ X.qPilot.badFinset, residueChar w ∈ primes)

include hbad in
private theorem logQAt_eq_zero_of_notMem (p : ℕ) (hp : p ∉ primes) : X.logQAt p = 0 := by
  unfold Corollary312VariantData.logQAt
  refine Finset.sum_eq_zero fun w hw => ?_
  exact (hp ((Finset.mem_filter.mp hw).2 ▸ hbad w.1 w.2)).elim

include hbad in
private theorem sum_scaled_logQAt (c : ℝ) :
    (∑ p ∈ primes, -c * (X.logQAt p / (2 * (X.data.ℓ : ℝ)))) = c * X.qPilot.lhs := by
  have hsum : ∑ p ∈ primes, X.logQAt p = X.qPilot.logQ := by
    unfold Corollary312VariantData.logQAt QPilotData.logQ
    exact Finset.sum_fiberwise_of_maps_to (fun w _ => hbad w.1 w.2) _
  rw [← Finset.mul_sum, ← Finset.sum_div, hsum, QPilotData.lhs, QPilotData.absLogQ,
    neg_mul, mul_neg]

end QPilot

private theorem average_capsule_volumes (n : ℕ) (hn : 0 < n) (q : ℝ) :
    (∑ i : Fin n, (((i.1 + 1 : ℕ) : ℝ) ^ 2 * q +
      ((i.1 + 2 : ℕ) : ℝ) * Real.log Real.pi)) / (n : ℝ) =
      (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6) * q +
        (((n : ℝ) + 3) / 2) * Real.log Real.pi := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  calc
    _ = (∑ i : Fin n, (Real.log Real.pi * ((i : ℝ) + 2) +
          q * ((i : ℝ) + 1) ^ 2 + 0)) / (n : ℝ) := by
      refine congrArg (fun s : ℝ => s / (n : ℝ)) (Finset.sum_congr rfl fun i _ => ?_)
      push_cast
      ring
    _ = _ := by
      rw [sum_affine_quadratic]
      apply (div_eq_iff hnR).2
      ring

private theorem finsum_rationalPlace_eq_add (volume : RationalPlace → ℝ)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime) (finiteVolume : ℕ → ℝ)
    (finiteTotal archVolume : ℝ)
    (hfinite : ∀ p : Nat.Primes, volume (.finite p) = finiteVolume p)
    (hzero : ∀ p : Nat.Primes, (p : ℕ) ∉ primes → finiteVolume p = 0)
    (harch : volume .infinite = archVolume)
    (hsum : (∑ p ∈ primes, finiteVolume p) = finiteTotal) :
    (∑ᶠ q, volume q) = finiteTotal + archVolume := by
  calc
    _ = volume .infinite + ∑ p ∈ primes, finiteVolume p :=
      finsum_rationalPlace_eq volume primes hprime finiteVolume hfinite hzero
    _ = archVolume + finiteTotal := congrArg₂ (fun a b : ℝ => a + b) harch hsum
    _ = _ := add_comm _ _

private noncomputable abbrev capsuleSquare {n : ℕ} (i : Fin n) : ℝ :=
  ((i.1 + 1 : ℕ) : ℝ) ^ 2

private noncomputable abbrev capsuleArchVolume {n : ℕ} (i : Fin n) : ℝ :=
  ((i.1 + 2 : ℕ) : ℝ) * Real.log Real.pi

noncomputable abbrev capsuleVolumeFormula {n : ℕ} (q : ℝ) (i : Fin n) : ℝ :=
  capsuleSquare i * q + capsuleArchVolume i

noncomputable abbrev averageSlope (n : ℝ) : ℝ :=
  (n + 1) * (2 * n + 1) / 6

noncomputable abbrev averageArchVolume (n : ℝ) : ℝ :=
  ((n + 3) / 2) * Real.log Real.pi

private theorem average_eq_of_capsule_volumes (n : ℕ) (hn : 0 < n)
    (volume : Fin n → ℝ) (q : ℝ)
    (hcapsule : ∀ i, volume i = capsuleVolumeFormula q i) :
    (∑ i, volume i) / (n : ℝ) = averageSlope (n : ℝ) * q + averageArchVolume (n : ℝ) := by
  calc
    _ = (∑ i : Fin n, capsuleVolumeFormula q i) / (n : ℝ) :=
      congrArg (fun s : ℝ => s / (n : ℝ)) (Finset.sum_congr rfl fun i _ => hcapsule i)
    _ = _ := average_capsule_volumes n hn q

section ThetaLocalVolume

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG} {D : InitialThetaData AG TG}
variable {LT : LocalTheory.{u, v} D.Kt} (TL : ThetaLocalData D LT) (QI : QPilotInputs D)

local notation "ThetaVariant" =>
  (concreteVariantData D LT TL QI)

private theorem variant_rhs_eq :
    (ThetaVariant).rhsData.rhs = TL.rhsData.rhs := rfl

private theorem procession_length_pos : 0 < (D.ℓ - 1) / 2 := by
  have h5 := D.prime.five_le
  change 5 ≤ D.ℓ at h5
  omega

-- Use a common expression for each packet volume in the hypotheses and the sums.
private noncomputable abbrev hullPacketVolume (i : Fin ((D.ℓ - 1) / 2))
    (q : RationalPlace) : ℝ :=
  let R : RHSData.{u, v} D := TL.rhsData
  R.vol.packetVol i q ((R.thetaHull i).region q)

noncomputable abbrev hullGlobalVolume (i : Fin ((D.ℓ - 1) / 2)) : ℝ :=
  let R : RHSData.{u, v} D := TL.rhsData
  R.vol.globalVol (R.thetaHull i)

noncomputable abbrev signedQPilotVolume : ℝ := (ThetaVariant).qPilot.lhs

private noncomputable abbrev finitePacketFormula (factor : ℝ) (p : ℕ) : ℝ :=
  -factor * ((ThetaVariant).logQAt p / (2 * (D.ℓ : ℝ)))

private theorem globalVol_thetaHull_eq_finsum (i : Fin ((D.ℓ - 1) / 2)) :
    hullGlobalVolume TL i = ∑ᶠ q, hullPacketVolume TL i q := rfl

private theorem rhsData_rhs_eq_average :
    let n : ℕ := (D.ℓ - 1) / 2
    TL.rhsData.rhs = (∑ i : Fin n, hullGlobalVolume TL i) / (n : ℝ) := rfl

private theorem variant_badChars :
    ∀ w ∈ (ThetaVariant).qPilot.badFinset, residueChar w ∈ TL.badChars := by
  change ∀ w ∈ QI.qPilot.badFinset, residueChar w ∈ TL.badChars
  exact fun w hw => TL.bad_residueChar_mem w (QI.qPilot.mem_bad hw)

private theorem scaled_logQAt_eq_zero (factor : ℝ) (p : ℕ) (hp : p ∉ TL.badChars) :
    finitePacketFormula TL QI factor p = 0 := by
  change -factor * ((ThetaVariant).logQAt p / (2 * (D.ℓ : ℝ))) = 0
  have hz : (ThetaVariant).logQAt p = 0 :=
    logQAt_eq_zero_of_notMem (concreteVariantData.{u, v} D LT TL QI)
      TL.badChars (variant_badChars TL QI) p hp
  rw [hz, zero_div, mul_zero]

private theorem sum_scaled_concrete_logQAt (factor : ℝ) :
    (∑ p ∈ TL.badChars, finitePacketFormula TL QI factor p) =
      factor * signedQPilotVolume TL QI :=
  sum_scaled_logQAt (concreteVariantData.{u, v} D LT TL QI)
    TL.badChars (variant_badChars TL QI) factor

variable (hfinite : ∀ (i : Fin ((D.ℓ - 1) / 2)) (p : Nat.Primes),
  hullPacketVolume TL i (.finite p) = finitePacketFormula TL QI (capsuleSquare i) p)
variable (harch : ∀ i : Fin ((D.ℓ - 1) / 2),
  hullPacketVolume TL i .infinite = capsuleArchVolume i)

include hfinite harch in
/-- Sum the local packet volumes for one capsule of this theta hull. -/
theorem globalVol_thetaHull_eq_of_packetVolumes (i : Fin ((D.ℓ - 1) / 2)) :
    hullGlobalVolume TL i = capsuleVolumeFormula (signedQPilotVolume TL QI) i := by
  have hfiniteAt := hfinite i
  have harchAt := harch i
  have hzero (p : Nat.Primes) (hp : (p : ℕ) ∉ TL.badChars) :
      finitePacketFormula TL QI (capsuleSquare i) p = 0 :=
    scaled_logQAt_eq_zero TL QI (capsuleSquare i) p hp
  have hsum := sum_scaled_concrete_logQAt TL QI (capsuleSquare i)
  have hvol := finsum_rationalPlace_eq_add (hullPacketVolume TL i)
    TL.badChars TL.badChars_prime (finitePacketFormula TL QI (capsuleSquare i))
    (capsuleSquare i * signedQPilotVolume TL QI) (capsuleArchVolume i)
    hfiniteAt hzero harchAt hsum
  exact (globalVol_thetaHull_eq_finsum TL i).trans hvol

include hfinite harch in
/-- Average the capsule volumes over the standard procession. -/
theorem rhs_thetaHull_eq_of_packetVolumes :
    let n : ℝ := (((D.ℓ - 1) / 2 : ℕ) : ℝ)
    (ThetaVariant).rhsData.rhs =
      averageSlope n * signedQPilotVolume TL QI + averageArchVolume n := by
  have hcapsule := globalVol_thetaHull_eq_of_packetVolumes (LT := LT) TL QI hfinite harch
  have havg := average_eq_of_capsule_volumes ((D.ℓ - 1) / 2) (procession_length_pos (D := D))
    (hullGlobalVolume TL) (signedQPilotVolume TL QI) hcapsule
  exact (variant_rhs_eq TL QI).trans ((rhsData_rhs_eq_average TL).trans havg)

private theorem corollary312Variant_iff_of_rhs (X : Corollary312VariantData.{u, v} AG TG)
    (a b : ℝ) (hrhs : X.rhsData.rhs = a * X.qPilot.lhs + b) :
    Corollary312Variant X ↔ (a - 1) * X.qPilot.absLogQ ≤ b := by
  change X.qPilot.lhs ≤ X.rhsData.rhs ↔ _
  rw [hrhs, QPilotData.lhs, mul_neg, neg_add_eq_sub, le_sub_iff_add_le, neg_add_eq_sub,
    sub_mul, one_mul]

include hfinite harch in
/-- Express the volume comparison as a bound on the absolute q-pilot logarithm. -/
theorem corollary312Variant_iff_absLogQ_bound_of_packetVolumes :
    let n : ℝ := (((D.ℓ - 1) / 2 : ℕ) : ℝ)
    Corollary312Variant (ThetaVariant) ↔
      (averageSlope n - 1) * (ThetaVariant).qPilot.absLogQ ≤ averageArchVolume n := by
  let n : ℝ := (((D.ℓ - 1) / 2 : ℕ) : ℝ)
  have hrhs := rhs_thetaHull_eq_of_packetVolumes (LT := LT) TL QI hfinite harch
  exact corollary312Variant_iff_of_rhs (concreteVariantData.{u, v} D LT TL QI)
    (averageSlope n) (averageArchVolume n) hrhs

end ThetaLocalVolume

end AbcAdaptation.Reference.Iut.ThetaLocalData
