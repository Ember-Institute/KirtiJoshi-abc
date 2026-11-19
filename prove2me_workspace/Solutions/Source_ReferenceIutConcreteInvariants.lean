/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/Invariants.lean
-/
import Solutions.Source_ReferenceIutConcreteThetaRegion
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants
import Definitions.Def_AbcAdaptation_Reference_Iut_Implication_Invariants
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

universe u v

open NumberField IsDedekindDomain
open scoped BigOperators

namespace LocalTheory

variable {K : Type u} [Field K] [NumberField K] (LT : LocalTheory.{u, v} K)

/-- The residue characteristics of the primes ramified in `K`, as a finite set. -/
noncomputable def ramifiedChars : Finset ℕ :=
  (LT.ramified_finite.toFinset).image residueChar

/-- `log(d^K_p) = ∑_{v ∣ p} w_v·d_v·log p` (the contribution of `p` to the normalized
degree of the different of `K`), and `0` at non-primes. -/
noncomputable def logDK (p : ℕ) : ℝ :=
  if hp : p.Prime then
    ∑ v : LT.Fiber (.finite ⟨p, hp⟩),
      LT.weight _ v * differentExponent K (LT.fiberPlace v) * Real.log p
  else 0

lemma differentExponent_nonneg (w : FinitePlace K) : 0 ≤ differentExponent K w :=
  div_nonneg (by positivity) (by positivity)

lemma logDK_nonneg (p : ℕ) : 0 ≤ LT.logDK p := by
  unfold LocalTheory.logDK
  split_ifs with hp
  · exact Finset.sum_nonneg fun v _ => mul_nonneg
      (mul_nonneg (LT.weight_pos _ v).le (differentExponent_nonneg _))
      (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
  · exact le_rfl

end LocalTheory

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}

namespace ThetaLocalData

variable (TL : ThetaLocalData D LT)

/-- **The distinguished primes** `V_ℚ^dst`: `2, 3, 5, ℓ`, the bad residue characteristics,
and the primes ramified in `K` ((D6)/(D7), as the definition). -/
noncomputable def dst : Finset ℕ :=
  {2, 3, 5, D.ℓ} ∪ TL.badChars ∪ LT.ramifiedChars

lemma dst_prime (p : ℕ) (hp : p ∈ TL.dst) : p.Prime := by
  simp only [dst, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    LocalTheory.ramifiedChars, Finset.mem_image, Set.Finite.mem_toFinset] at hp
  rcases hp with ((rfl | rfl | rfl | rfl) | hb) | ⟨w, _, rfl⟩
  · exact Nat.prime_two
  · exact Nat.prime_three
  · exact Nat.prime_five
  · exact D.prime.ℓ_prime
  · exact TL.badChars_prime _ hb
  · exact LT.residueChar_prime w

lemma mem_dst_of_ramified (w : FinitePlace D.Kt) (hw : ramIdx D.Kt w ≠ 1) :
    residueChar w ∈ TL.dst := by
  refine Finset.mem_union_right _ ?_
  simp only [LocalTheory.ramifiedChars, Finset.mem_image, Set.Finite.mem_toFinset]
  exact ⟨w, hw, rfl⟩

lemma mem_dst_of_badChars (p : ℕ) (hp : p ∈ TL.badChars) : p ∈ TL.dst :=
  Finset.mem_union_left _ (Finset.mem_union_right _ hp)

lemma two_mem_dst : 2 ∈ TL.dst := by
  refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
  simp

lemma logDK_eq_zero (p : ℕ) (hp : p ∉ TL.dst) : LT.logDK p = 0 := by
  unfold LocalTheory.logDK
  split_ifs with hpp
  · refine Finset.sum_eq_zero fun v _ => ?_
    have hunr : ramIdx D.Kt (LT.fiberPlace v) = 1 := by
      by_contra hne
      apply hp
      apply Eq.mp (congrArg (fun q : ℕ => q ∈ TL.dst)
        (LT.residueChar_fiberPlace (p := ⟨p, hpp⟩) v))
      exact TL.mem_dst_of_ramified _ hne
    simp [differentExponent, LT.ordDifferent_eq_zero _ hunr]
  · rfl

end ThetaLocalData

lemma logDifferentDeg_nonneg (L : Type*) [Field L] [NumberField L] :
    0 ≤ logDifferentDeg L := by
  unfold logDifferentDeg
  apply div_nonneg _ (by positivity)
  apply Real.log_nonneg
  have h : Ideal.absNorm (differentIdeal ℤ (𝓞 L)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact differentIdeal_ne_bot
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h

lemma logConductorDegOf_nonneg (F : Type*) [Field F] [NumberField F]
    (E : WeierstrassCurve F) [E.IsElliptic]
    (VBad : Set (FinitePlace ↥(fieldOfModuli F E))) : 0 ≤ logConductorDegOf F E VBad := by
  unfold logConductorDegOf
  apply div_nonneg _ (by positivity)
  apply finsum_nonneg
  intro 𝔭
  split_ifs
  · exact Real.log_nonneg
      (by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭.maximalIdeal).le)
  · exact le_rfl

namespace InitialThetaData

variable (D : InitialThetaData AG TG)

/-- `d_mod = [F_mod : ℚ]`. -/
noncomputable abbrev dmod : ℕ := Module.finrank ℚ ↥(fieldOfModuli D.F D.E)

lemma one_le_dmod : 1 ≤ D.dmod := Module.finrank_pos

/-- The tripodal field `F_tpd` of the Θ-data (`Iut.tripodalFieldOf`). -/
noncomputable abbrev tripodalField : IntermediateField ℚ D.F := tripodalFieldOf D.F D.E

/-- The conductor invariant `log(f_{F_tpd})` of the Θ-data (`Iut.logConductorDegOf`). -/
noncomputable abbrev logConductorDeg : ℝ := logConductorDegOf D.F D.E D.VBad

lemma logConductorDeg_nonneg : 0 ≤ D.logConductorDeg := logConductorDegOf_nonneg _ _ _

end InitialThetaData

variable (TL : ThetaLocalData D LT) (QI : QPilotInputs D)

/-- **The concrete invariants of Theorem 1.10** for the concrete variant data, with
`e_mod := d_mod` (Theorem 1.10 holds with `e_mod` replaced by any `e ≥ e_mod`, and
Corollary 2.2 uses `d*_mod` anyway), `log(d_{F_tpd})`, `log(f_{F_tpd})` the different and
conductor degrees of the tripodal field, the distinguished primes and `log(d^K_p)`. -/
noncomputable def ThetaLocalData.invariants :
    Theorem110Invariants (concreteVariantData D LT TL QI) where
  emod := D.dmod
  one_le_emod := D.one_le_dmod
  emod_le_dmod := le_rfl
  logDtpd := logDifferentDeg ↥D.tripodalField
  logDtpd_nonneg := logDifferentDeg_nonneg _
  logFtpd := D.logConductorDeg
  logFtpd_nonneg := D.logConductorDeg_nonneg
  dst := TL.dst
  dst_prime := TL.dst_prime
  logDK := LT.logDK
  logDK_nonneg := LT.logDK_nonneg
  logDK_eq_zero := TL.logDK_eq_zero

/-- **The tower arithmetic of Theorem 1.10** (IUT IV, Steps (ii)–(iii) and (R4)): standard
algebraic number theory of the tower `F_mod ⊆ F_tpd ⊆ F ⊆ K = F(E[ℓ])`, from
Proposition 1.3 (differents in towers of local fields, taxis #1463), Proposition 1.8
(reduction theory, taxis #5; Néron–Ogg–Shafarevich, taxis #73) and the Galois-group
inclusions `Gal(K/F) ↪ GL₂(𝔽_ℓ)`, `Gal(F/F_tpd) ↪ GL₂(𝔽_3) × GL₂(𝔽_5) × ℤ/2`,
`Gal(F_tpd/F_mod) ↪ GL₂(𝔽_2)`. With `e_mod` replaced by `d_mod` and `e*_mod = 552960·d_mod`.
The three bounds are stated on the local and global data of the same torsion field. -/
structure TowerArithmetic (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt)
    (TL : ThetaLocalData D LT) : Prop where
  /-- **(R4)**: if `e_v > p_v − 2` then `p_v ≤ e*_mod·ℓ` and
  `log e_v ≤ −3 + 4·log(e*_mod·ℓ)`. -/
  ramIdx_bound : ∀ v : FinitePlace D.Kt, residueChar v - 2 < ramIdx D.Kt v →
    residueChar v ≤ 552960 * D.dmod * D.ℓ ∧
      Real.log (ramIdx D.Kt v) ≤ -3 + 4 * Real.log (((552960 * D.dmod : ℕ) : ℝ) * D.ℓ)
  /-- **Step (ii)**: `log(d_K) ≤ log(d_{F_tpd}) + log(f_{F_tpd}) + 2·log ℓ + 21`. -/
  step_ii : ∑ p ∈ TL.dst, LT.logDK p ≤
    logDifferentDeg ↥D.tripodalField + D.logConductorDeg + 2 * Real.log D.ℓ + 21
  /-- **Step (iii)**: `log(s^ℚ) ≤ 2·d_mod·(log(d_{F_tpd}) + log(f_{F_tpd})) + 5 + log ℓ`. -/
  step_iii : ∑ p ∈ TL.dst, Real.log p ≤
    2 * D.dmod * (logDifferentDeg ↥D.tripodalField + D.logConductorDeg) + 5 + Real.log D.ℓ

variable {TL QI}

/-- The residue characteristics of the bad places of `F` are distinguished ((D2)). -/
lemma ThetaLocalData.bad_mem_dst (w : FinitePlace D.F)
    (hw : w ∈ (concreteVariantData D LT TL QI).qPilot.badFinset) : residueChar w ∈ TL.dst :=
  TL.mem_dst_of_badChars _ (TL.bad_residueChar_mem w
    ((concreteVariantData D LT TL QI).qPilot.mem_bad hw))

/-- The arithmetic certificate of Theorem 1.10 for the concrete invariants, from `ℓ ≥ 7`
and the tower arithmetic. -/
theorem TowerArithmetic.certificate (TA : TowerArithmetic D LT TL) (h7 : 7 ≤ D.ℓ) :
    Theorem110Certificate (TL.invariants QI) where
  seven_le := h7
  bad_mem_dst := ThetaLocalData.bad_mem_dst (QI := QI)
  step_ii := by exact TA.step_ii
  step_iii := by exact TA.step_iii

end AbcAdaptation.Reference.Iut
