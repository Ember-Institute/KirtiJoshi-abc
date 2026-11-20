import Solutions.Source_TripodRationalLegendreFiveTransport
import Solutions.Source_TripodFinitePrimeCounting
import Solutions.Source_ReferenceIutConcreteLocalArithmetic
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_UniformizerSupply
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open AbcAdaptation.Reference.Iut

/-- The rational family stays uniformly bounded at the real places and above 2. -/
noncomputable def rationalLegendreFiveLocus : CompactlyBounded where
  V := {2}
  prime := by
    intro p hp
    simpa only [Finset.mem_singleton.mp hp] using Nat.prime_two
  two_mem := Finset.mem_singleton_self 2
  c := Real.log 3

private theorem finitePlace_apply_natCast_eq_one_of_not_dvd
    {F : Type*} [Field F] [NumberField F] (v : FinitePlace F) (a : ℕ)
    (ha : ¬ residueChar v ∣ a) : v (a : F) = 1 := by
  have hnon : (a : 𝓞 F) ∉ v.maximalIdeal.asIdeal := by
    intro hw
    have hz : (a : 𝓞 F ⧸ v.maximalIdeal.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v.maximalIdeal.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hw
    exact ha ((ringChar.spec _ a).mp hz)
  have hu : v.maximalIdeal.valuation F (a : F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 F) F), valuation_eq_one_iff_notMem]
    exact hnon
  rw [← FinitePlace.norm_embedding_eq, norm_eq_one_iff_valued, FinitePlace.embedding_apply,
    valuedAdicCompletion_eq_valuation', hu]

private theorem abs_log_le_log_three {r : ℝ} (hlo : 1 / 3 ≤ r) (hhi : r ≤ 1) :
    |Real.log r| ≤ Real.log 3 := by
  rw [abs_of_nonpos (Real.log_nonpos (by linarith) hhi)]
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 3) hlo
  rw [one_div, Real.log_inv] at h
  linarith only [h]

/-- All members of the family lie in one fixed compactly bounded locus. -/
theorem rationalLegendreFivePoint_mem_locus (m : ℕ) :
    rationalLegendreFivePoint m ∈ rationalLegendreFiveLocus.set := by
  classical
  let x := rationalLegendreFivePoint m
  let F := ↥(fieldOf x.1)
  let q := rationalLegendreFiveParam m
  have hg : gen x.1 = algebraMap ℚ F q := Subtype.ext rfl
  have hdeg : Module.finrank ℚ F = 1 :=
    (deg_eq_finrank x.1).symm.trans (rationalLegendreFivePoint_deg m)
  refine CompactlyBounded.mem_set.mpr ⟨?_, ?_⟩
  · intro v hv
    have hp : residueChar v = 2 := Finset.mem_singleton.mp hv
    let a : ℕ := 5 ^ m
    let b : ℕ := 2 * a + 1
    let e : ℕ := 2 * (a / 4) + 1
    have ha4 : a % 4 = 1 := by
      dsimp only [a]
      rw [Nat.pow_mod]
      norm_num
    have hae : a + 1 = 2 * e := by dsimp only [e]; omega
    have ha : v (a : F) = 1 :=
      finitePlace_apply_natCast_eq_one_of_not_dvd v a (by rw [hp]; omega)
    have hb : v (b : F) = 1 :=
      finitePlace_apply_natCast_eq_one_of_not_dvd v b (by rw [hp]; dsimp only [b]; omega)
    have he : v (e : F) = 1 :=
      finitePlace_apply_natCast_eq_one_of_not_dvd v e (by rw [hp]; dsimp only [e]; omega)
    have hb0 : (b : F) ≠ 0 := Nat.cast_ne_zero.mpr (by dsimp only [b]; omega)
    have hq : q = (a : ℚ) / (b : ℚ) := by simp [q, a, b, rationalLegendreFiveParam]
    have hgen : gen x.1 = (a : F) / (b : F) := by
      rw [hg, hq, map_div₀, map_natCast, map_natCast]
    have hnum : (a : F) - (b : F) = -(2 * (e : F)) := by
      have hcast : (a : F) + 1 = 2 * (e : F) := by exact_mod_cast hae
      calc
        (a : F) - (b : F) = -((a : F) + 1) := by
          simp only [b, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
          ring
        _ = _ := by rw [hcast]
    have hqval : v (gen x.1) = 1 := by
      rw [hgen, map_div₀, ha, hb, div_one]
    have hqsub : v (gen x.1 - 1) = v (2 : F) := by
      rw [hgen, div_sub_one hb0, hnum, map_div₀, map_neg_eq_map, map_mul, he, hb, mul_one, div_one]
    have hlocal_le : localDeg F v ≤ 1 := by
      have hfilter : ({v} : Finset (FinitePlace F)).filter (fun w => residueChar w = 2) = {v} := by
        exact Finset.filter_eq_self.mpr (fun w hw => (Finset.mem_singleton.mp hw).symm ▸ hp)
      have h := sum_localDeg_filter_le ({v} : Finset (FinitePlace F)) 2
      rwa [hfilter, Finset.sum_singleton, hdeg] at h
    have hlocal : localDeg F v = 1 :=
      le_antisymm hlocal_le (Nat.mul_pos (ramIdx_pos' v) (inertDeg_pos' v))
    have horder := LocalConstruct.ordp_p v
    change -Real.log ‖algebraMap F (completionAt F v) (residueChar v : F)‖ /
      ((localDeg F v : ℝ) * Real.log (residueChar v)) = 1 at horder
    have hemb : algebraMap F (completionAt F v) (2 : F) =
        FinitePlace.embedding v.maximalIdeal (2 : F) := rfl
    simp only [hp, hlocal, Nat.cast_ofNat, Nat.cast_one, one_mul] at horder
    rw [hemb, FinitePlace.norm_embedding_eq] at horder
    have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlog : Real.log (v (2 : F)) = -Real.log 2 := by
      have h := (div_eq_iff hl2.ne').mp horder
      linarith only [h]
    change |Real.log (v (gen x.1))| ≤ Real.log 3 ∧
      |Real.log (v (gen x.1 - 1))| ≤ Real.log 3
    rw [hqval, hqsub, hlog, Real.log_one, abs_zero, abs_neg, abs_of_pos hl2]
    exact ⟨Real.log_nonneg (by norm_num), Real.log_le_log (by norm_num) (by norm_num)⟩
  · intro w
    have hsub : gen x.1 - 1 = algebraMap ℚ F (q - 1) := by rw [hg, map_sub, map_one]
    change |Real.log (w (gen x.1))| ≤ Real.log 3 ∧
      |Real.log (w (gen x.1 - 1))| ≤ Real.log 3
    rw [hsub, hg]
    change |Real.log (w (q : F))| ≤ Real.log 3 ∧
      |Real.log (w ((q - 1 : ℚ) : F))| ≤ Real.log 3
    simp only [InfinitePlace.map_ratCast, ← Rat.norm_cast_real, Real.norm_eq_abs,
      Rat.cast_sub, Rat.cast_one]
    have hlo : (1 / 3 : ℝ) ≤ (q : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr (rationalLegendreFiveParam_bounds m).1
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
    have hhi : (q : ℝ) < 1 / 2 := by
      have h := (Rat.cast_lt (K := ℝ)).mpr (rationalLegendreFiveParam_bounds m).2
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ q), abs_of_nonpos (by linarith : (q : ℝ) - 1 ≤ 0)]
    exact ⟨abs_log_le_log_three hlo (by linarith), abs_log_le_log_three (by linarith) (by linarith)⟩

end AbcAdaptation.Tripod
