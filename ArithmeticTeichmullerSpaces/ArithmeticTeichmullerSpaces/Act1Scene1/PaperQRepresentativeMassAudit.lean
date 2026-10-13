import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQRepresentativeSelectedQRootBridge

/-!
source-id: JT-SCENE1-PAPER-REPRESENTATIVE-MASS-AUDIT
source: the q-pilot arithmetic weight bound over each rational prime and the
existing representative accounting certificate; Joshi III `cor:cor312` uses
all selected representatives in each nonempty prime fibre.
fidelity: proves the restrictions imposed by requiring mass one at every
representative. A prime-preserving source map forces the representative prime
label to be injective, including on the actual canonical section-link carrier.
It does not assert that the prime-preserving map or a two-place countermodel
has already been constructed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open scoped BigOperators

universe u

noncomputable section
variable {K : Type u} [Field K] [NumberField K]
variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p} {P : Corollary312QPilotData p T}

namespace Corollary312QPilotPaperRepresentativeAccounting

theorem representativeOfSource_surjective
    (A : Corollary312QPilotPaperRepresentativeAccounting p T P) :
    Function.Surjective A.representativeOfSource := by
  classical
  intro r
  by_contra h
  have hne : ∀ w, A.representativeOfSource w ≠ r := by
    intro w hw
    exact h ⟨w, hw⟩
  have hmass := A.weight_fiber_sum_eq_one r
  simp [hne] at hmass

private theorem source_prime_mass_le_one (q : ℕ) (hq : q.Prime) :
    (∑ w : P.badFinset,
      if Arithmetic.residueChar w.1 = q then Arithmetic.qPilotWeight w.1 else 0) ≤ 1 := by
  classical
  have h := Arithmetic.qPilotWeight_sum_le_one_of_residueChar_filter P.badFinset q hq
  rw [Finset.sum_filter] at h
  have hsum :
      (∑ w : P.badFinset,
        if Arithmetic.residueChar w.1 = q then Arithmetic.qPilotWeight w.1 else 0) =
      ∑ w ∈ P.badFinset,
        if Arithmetic.residueChar w = q then Arithmetic.qPilotWeight w else 0 := by
    refine Finset.sum_bij (fun w _ => w.1) ?_ ?_ ?_ ?_
    · intro w hw
      exact w.2
    · intro w hw v hv h
      exact Subtype.ext h
    · intro w hw
      exact ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩
    · intro w hw
      rfl
  rw [hsum]
  exact h

theorem primeLabel_injective
    (A : Corollary312QPilotPaperRepresentativeAccounting p T P)
    (primeLabel : A.representative → ℕ)
    (hPrime : ∀ w : P.badFinset,
      Arithmetic.residueChar w.1 = primeLabel (A.representativeOfSource w)) :
    Function.Injective primeLabel := by
  classical
  let := A.representativeDecidableEq
  intro r s hrs
  by_contra hne
  obtain ⟨w₀, hw₀⟩ := A.representativeOfSource_surjective p r
  have hq : (primeLabel r).Prime := by
    rw [← hw₀, ← hPrime w₀]
    exact Arithmetic.residueChar_prime w₀.1
  have hlocal (w : P.badFinset) :
      (if A.representativeOfSource w = r then Arithmetic.qPilotWeight w.1 else 0) +
        (if A.representativeOfSource w = s then Arithmetic.qPilotWeight w.1 else 0) ≤
      (if Arithmetic.residueChar w.1 = primeLabel r then
        Arithmetic.qPilotWeight w.1 else 0) := by
    have hnonneg := (Arithmetic.qPilotWeight_pos w.1).le
    by_cases hr : A.representativeOfSource w = r
    · have hs : A.representativeOfSource w ≠ s := by
        intro hs
        exact hne (hr.symm.trans hs)
      have hp : Arithmetic.residueChar w.1 = primeLabel r := (hPrime w).trans (congrArg primeLabel hr)
      simp only [if_pos hr, if_neg hs, if_pos hp, add_zero, le_refl]
    · by_cases hs : A.representativeOfSource w = s
      · have hp : Arithmetic.residueChar w.1 = primeLabel r := by
          rw [hPrime w, hs, hrs]
        simp only [if_neg hr, if_pos hs, if_pos hp, zero_add, le_refl]
      · simp only [if_neg hr, if_neg hs, zero_add]
        split_ifs <;> positivity
  have hsum := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset P.badFinset)) => hlocal w)
  rw [Finset.sum_add_distrib, A.weight_fiber_sum_eq_one r,
    A.weight_fiber_sum_eq_one s] at hsum
  have hbound := source_prime_mass_le_one (P := P) p (primeLabel r) hq
  linarith

end Corollary312QPilotPaperRepresentativeAccounting

namespace Corollary312PaperRepresentativeSectionLinkAccounting

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-- The mass-one certificate permits at most one canonical section-link place
above each rational prime if its source map preserves that prime. -/
theorem sectionLink_residueChar_injective
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {T : Corollary312Data D.F O p} {P : Corollary312QPilotData p T}
    (A : Corollary312QPilotPaperRepresentativeAccounting p T P)
    (theta : ThetaPilotData ↥D.prime.torsionField) (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData ↥D.prime.torsionField)
    (ramification : Arithmetic.RamificationProfile ↥D.prime.torsionField)
    (logVolume : ℝ) (processionLength : ℕ)
    (B : Corollary312PaperRepresentativeSectionLinkAccounting D p A theta thetaBase
      packetHull heightData ramification logVolume processionLength)
    (hPrime : ∀ w : P.badFinset,
      Arithmetic.residueChar w.1 =
        Arithmetic.residueChar (B.representativeLinkEquiv (A.representativeOfSource w)).1) :
    Function.Injective (fun w :
      {w : NumberField.FinitePlace ↥D.prime.torsionField //
        w ∈ (AdelicThetaLinkData.ofInitialThetaOddTateSection D theta thetaBase
          packetHull heightData ramification logVolume processionLength).places} =>
      Arithmetic.residueChar w.1) := by
  have h := A.primeLabel_injective p
    (fun r => Arithmetic.residueChar (B.representativeLinkEquiv r).1) hPrime
  intro w v hwv
  apply B.representativeLinkEquiv.symm.injective
  apply h
  simpa only [Equiv.apply_symm_apply] using hwv

end Corollary312PaperRepresentativeSectionLinkAccounting

end
end JoshiTeich.Act1Scene1
