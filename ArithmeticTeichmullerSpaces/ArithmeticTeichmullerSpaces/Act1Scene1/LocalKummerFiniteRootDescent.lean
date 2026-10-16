import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerCoefficientKernel
import Mathlib.FieldTheory.Galois.Infinite

/-!
source-id: JT-SCENE1-KUMMER-FINITE-ROOT-DESCENT
source: finite-level Tate coordinates, standard H1 equality modulo
coboundaries and actual Galois fixed-field descent; Joshi III 3214--3236.
fidelity: divisibility of a p-power multiple of an integral Kummer class
forces a concrete finite root in the base field. The competing integral
class can be arbitrary, not necessarily a Kummer class.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] [IsGalois K Ω] (p : ℕ) [Fact p.Prime]

theorem exists_root_of_class_divisibility {a : K} (R : RootTower (Ω := Ω) p a)
    (ha : a ≠ 0) (m n : ℕ)
    (x : continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p))
    (hx : (p ^ (m + n)) • x = (p ^ n) •
      padicClassOfCocycle p (R.continuousCocycleValue (Fact.out : p.Prime).pos ha)) :
    ∃ b : K, b ^ (p ^ (m + n)) = a ^ (p ^ n) := by
  obtain ⟨c, rfl⟩ := toPadicH1_surjective p x
  induction c using Quotient.inductionOn with
  | h f =>
    let X := padicTateTopRep (K := K) (Ω := Ω) p
    let g := R.continuousCocycleValue (Fact.out : p.Prime).pos ha
    let F := padicAdditiveCocycle p f
    let H := padicAdditiveCocycle p g
    have he : ContinuousH1Homogeneous.classOf X (((p ^ (m + n) : ℕ) : ℤ_[p]) • F)
        (ContinuousH1Homogeneous.cocycle_smul_law X _ F (padicAdditiveCocycle_law p f)) =
        ContinuousH1Homogeneous.classOf X (((p ^ n : ℕ) : ℤ_[p]) • H)
        (ContinuousH1Homogeneous.cocycle_smul_law X _ H (padicAdditiveCocycle_law p g)) := by
      rw [ContinuousH1Homogeneous.classOf_smul X _ F (padicAdditiveCocycle_law p f),
        ContinuousH1Homogeneous.classOf_smul X _ H (padicAdditiveCocycle_law p g)]
      simp only [Nat.cast_smul_eq_nsmul]
      change (p ^ (m + n)) • ContinuousH1Homogeneous.classOf X F
          (padicAdditiveCocycle_law p f) =
        (p ^ n) • ContinuousH1Homogeneous.classOf X H
          (padicAdditiveCocycle_law p g) at hx
      exact hx
    obtain ⟨t, ht⟩ := (ContinuousH1Recognition.classOf_eq_iff X _ _ _ _).mp he
    change Additive (cyclotomicTateGroup p Ω) at t
    have hratio (σ : Ω ≃ₐ[K] Ω) :
        R.ratio σ (m + n) ^ (p ^ n) =
          σ (t.toMul.1 (m + n) : Ω) / (t.toMul.1 (m + n) : Ω) := by
      have hh := ht σ
      change (((p ^ n : ℕ) : ℤ_[p]) • Additive.ofMul (g.1 σ) -
          ((p ^ (m + n) : ℕ) : ℤ_[p]) • Additive.ofMul (f.1 σ)) =
        Additive.ofMul (σ • t.toMul) - t at hh
      rw [padic_smul_natCast, padic_smul_natCast] at hh
      have hs := congrArg (fun z : Additive (cyclotomicTateGroup p Ω) =>
        (z.toMul.1 (m + n) : Ω)) hh
      simp only [toMul_sub, toMul_nsmul, Subgroup.coe_div, Subgroup.coe_pow,
        Pi.div_apply, Pi.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
        toMul_ofMul] at hs
      have hf0 : ((f.1 σ).1 (m + n) : Ω) ^ (p ^ (m + n)) = 1 :=
        congrArg (fun z : Ωˣ => (z : Ω)) ((f.1 σ).2.1 (m + n))
      rw [hf0, div_one] at hs
      exact hs
    let bΩ : Ω := R.root (m + n) ^ (p ^ n) / (t.toMul.1 (m + n) : Ω)
    have hbΩ (σ : Ω ≃ₐ[K] Ω) : σ bΩ = bΩ := by
      have hr := hratio σ
      change (σ (R.root (m + n)) / R.root (m + n)) ^ (p ^ n) = _ at hr
      rw [div_pow] at hr
      have hR := pow_ne_zero (p ^ n) (R.root_ne_zero (Fact.out : p.Prime).pos ha (m + n))
      have ht0 := (t.toMul.1 (m + n)).ne_zero
      have hs0 : σ (t.toMul.1 (m + n) : Ω) ≠ 0 := by
        simpa only [map_zero] using σ.injective.ne ht0
      change σ (R.root (m + n) ^ (p ^ n) / (t.toMul.1 (m + n) : Ω)) = _
      rw [map_div₀, map_pow]
      apply (div_eq_div_iff hs0 ht0).mpr
      simpa only [mul_comm] using (div_eq_div_iff hR ht0).mp hr
    obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed bΩ).mpr hbΩ
    refine ⟨b, (algebraMap K Ω).injective ?_⟩
    rw [map_pow, hb]
    have htPow : (t.toMul.1 (m + n) : Ω) ^ (p ^ (m + n)) = 1 :=
      congrArg (fun z : Ωˣ => (z : Ω)) (t.toMul.2.1 (m + n))
    change (R.root (m + n) ^ (p ^ n) / (t.toMul.1 (m + n) : Ω)) ^ (p ^ (m + n)) = _
    rw [div_pow, htPow, div_one, ← pow_mul, Nat.mul_comm (p ^ n), pow_mul, R.root_pow_eq, map_pow]

end
end JoshiTeich.Act1Scene1.LocalKummer
