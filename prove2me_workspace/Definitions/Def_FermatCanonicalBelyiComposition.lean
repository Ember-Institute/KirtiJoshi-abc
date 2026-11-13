/-
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The genl contributors

Concrete Fermat adaptation of Genl/GeneralPosition/TheoremTwoOne.lean.
All heights and conductors below are the actual definitions in the imported
modules. No real-valued function is supplied as a theorem hypothesis.
-/
import Definitions.Def_FermatBelyiComparisons

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

/-- Noncritical selection, local compactness, concrete divisor existence,
and six explicit arithmetic/height facts imply the original fixed estimate.
The actual model and its affine identity are selected from the six-node
NoncriticalInput. The proof does not assume the parent estimate as a child. -/
theorem canonicalEstimate_of_belyi_children
    (hInput : ∀ N : ℕ, 3 < N → NoncriticalInput N)
    (hCompact : ∀ {N : ℕ} (M : Model N), PlacesDiscrete M →
      ResiduesFinite M → LocalCompactness M)
    (hRegular : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M),
      AvoidanceRegularity M hDVR)
    (hEmbedding : ∀ {N : ℕ} (M : Model N), ResiduesFinite M → EmbeddingBoundsToSet M)
    (hChoices : ∀ {N : ℕ} (M : Model N) (hDVR : PlacesDiscrete M),
      3 < N → ResiduesFinite M → ∀ (φ : M.K), IsBelyi M hDVR φ →
      ∀ hfin : (cusps M hDVR φ).Finite,
        Nonempty (ArithmeticDivisorChoices M hDVR φ hfin))
    (hDegree : CanonicalDegreeIdentity)
    (hCanonical : CanonicalHeightIdentification)
    (hHeight : BelyiHeightRelation)
    (hStrictHeight : DivisorDegreeHeightComparison)
    (hDifferent : BelyiDifferentConductorComparison)
    (hConductor : CuspConductorHeightComparison) : Fermat.CanonicalEstimate := by
  intro hII N hN d ε hε
  obtain ⟨M, hDVR, hRF, ⟨A⟩, hSelect, hFiniteCusps⟩ := hInput N hN
  have hBounded := boundedBelyiImages_of_children M hDVR A
    (hCompact M hDVR hRF) (hRegular M hDVR) hSelect (hEmbedding M hRF)
  by_contra hfail
  push_neg at hfail
  choose xs hxdeg hxfail using fun n : ℕ => hfail (n : ℝ)
  obtain ⟨φ, hφ, s, hs, K, hImages⟩ := hBounded d xs hxdeg
  have hfin := hFiniteCusps φ hφ
  obtain ⟨B⟩ := hChoices M hDVR hN hRF φ hφ hfin
  have hKdeg := hDegree M hDVR hN hRF B.canonical B.infinity B.adjunction
  have hKpos : 0 < divisorDegree M B.canonical.D := by
    rw [hKdeg]
    unfold planeCanonicalDegree
    have hNint : (3 : ℤ) < N := by exact_mod_cast hN
    nlinarith
  have hKposR : (0 : ℝ) < divisorDegree M B.canonical.D := by exact_mod_cast hKpos
  let ratio : ℝ := (divisorDegree M (cuspDivisor M hDVR φ hfin) : ℝ) /
    (planeCanonicalDegree N : ℝ)
  let q : ℝ := max ratio 0 + 1
  have hq : 0 < q := by dsimp [q]; linarith [le_max_right ratio 0]
  have hStrictQ : StrictQ M hDVR φ hfin q := by
    change ratio < q
    dsimp [q]
    linarith [le_max_left ratio 0]
  have hdegree : (divisorDegree M (cuspDivisor M hDVR φ hfin) : ℝ) <
      q * divisorDegree M B.canonical.D := by
    have hden : (0 : ℝ) < planeCanonicalDegree N := by
      rw [← hKdeg]
      exact hKposR
    have h := (div_lt_iff₀ hden).mp hStrictQ
    simpa only [hKdeg] using h
  obtain ⟨CK, hCK⟩ := hCanonical M hDVR hN hRF A
    B.canonical B.infinity B.adjunction B.canonicalPresentation
  obtain ⟨CB, hCB⟩ := hHeight M hDVR hRF A φ hφ hfin B
  obtain ⟨CQ, hCQ⟩ := hStrictHeight M hDVR hRF
    B.canonical.D (cuspDivisor M hDVR φ hfin)
    B.canonicalPresentation B.cuspPresentation q hKpos hdegree
  obtain ⟨CD, hCD⟩ := hDifferent M hDVR hRF A φ hφ hfin B.generators
  obtain ⟨CC, hCC⟩ := hConductor M hDVR hRF A φ hφ hfin
    B.generators B.cuspPresentation
  have hden : 0 < 1 + q * (1 + ε) := by nlinarith
  let δ : ℝ := ε / (1 + q * (1 + ε))
  have hδ : 0 < δ := div_pos hε hden
  have hkey : 1 + δ = (1 + ε) * (1 - δ * q) := by
    dsimp [δ]
    field_simp [hden.ne']
    <;> ring
  have hfactor : 0 < 1 - δ * q := by nlinarith
  obtain ⟨CT, hCT⟩ := hII d δ hδ K
  let C : ℝ := CT + CB + CK + (1 + δ) * (CD + CC) + δ * CQ + (δ * q) * CK
  have hchain : ∀ n : ℕ, Fermat.canonicalHeight (xs (s n)) ≤
      (1 + δ) * Fermat.logDiff (xs (s n)) +
        (δ * q) * Fermat.canonicalHeight (xs (s n)) + C := by
    intro n
    obtain ⟨hgood, hmem, hd⟩ := hImages n
    have ht := hCT (belyiImage M φ (affineLift M A (xs (s n)))) hmem hd
    have hk := abs_le.mp (hCK (xs (s n)))
    have hb := abs_le.mp (hCB (xs (s n)) hgood)
    have hd := mul_le_mul_of_nonneg_left (hCD (xs (s n)) hgood)
      (by linarith : 0 ≤ 1 + δ)
    have hc := mul_le_mul_of_nonneg_left (hCC (xs (s n)) hgood)
      (by linarith : 0 ≤ 1 + δ)
    have he := mul_le_mul_of_nonneg_left (hCQ (affineLift M A (xs (s n)))) hδ.le
    have hkupper : divHeight B.canonicalPresentation (affineLift M A (xs (s n))) ≤
        Fermat.canonicalHeight (xs (s n)) + CK := by linarith [hk.2]
    have hkq := mul_le_mul_of_nonneg_left hkupper (mul_nonneg hδ.le hq.le)
    dsimp [C]
    nlinarith [hk.1, hk.2, hb.1, hb.2]
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (1 - δ * q))
  have hsn : C / (1 - δ * q) < (s n : ℝ) :=
    hn.trans_le (by exact_mod_cast hs.id_le n)
  have hlarge : C < (1 - δ * q) * (s n : ℝ) := by
    have h := mul_lt_mul_of_pos_left hsn hfactor
    rwa [mul_div_cancel₀ _ hfactor.ne'] at h
  have hfailn := mul_lt_mul_of_pos_left (hxfail (s n)) hfactor
  have hbound := hchain n
  rw [hkey] at hbound
  nlinarith

end AbcAdaptation.Tripod.Fermat.Proper
