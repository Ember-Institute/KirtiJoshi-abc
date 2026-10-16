import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerTateCoordinateBound
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerFiniteLevelDetection
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerDividedIntegralLift

/-!
source-id: JT-SCENE1-KUMMER-FINITE-LEVEL-APPROXIMATION
source: actual finite-level Hilbert 90 sources, original Kummer roots and
primitive Tate level extension; Joshi III 3190--3236.
fidelity: every integral cocycle has, at each finite level, an exact matching
representative of an actual field-element Kummer class. The representative
differs from the ordinary Kummer cocycle by an explicit Tate coboundary.
The rational coordinate error is uniformly bounded by |p|^n.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]

def boundaryCocycle (t : cyclotomicTateGroup p Ω) : continuousCocycles (K := K) (Ω := Ω) p :=
  ⟨⟨fun σ => σ • t / t, by
      have hs := (continuous_tateAction (K := K) (Ω := Ω) p).comp
        (show Continuous (fun σ : Ω ≃ₐ[K] Ω => (σ, t)) from continuous_id.prodMk continuous_const)
      exact hs.div' continuous_const⟩, by
    intro σ τ
    change (σ * τ) • t / t = σ • (τ • t / t) * (σ • t / t)
    rw [mul_smul, smul_div']
    exact (div_mul_div_cancel _ _ _).symm⟩

def adjustCocycle (f : continuousCocycles (K := K) (Ω := Ω) p)
    (t : cyclotomicTateGroup p Ω) : continuousCocycles (K := K) (Ω := Ω) p :=
  multiplyCocycles f (boundaryCocycle p t)

theorem adjustCocycle_class (f : continuousCocycles (K := K) (Ω := Ω) p)
    (t : cyclotomicTateGroup p Ω) :
    padicClassOfCocycle p (adjustCocycle p f t) = padicClassOfCocycle p f := by
  symm
  apply (padicClassOfCocycle_eq_iff p f _).mpr
  refine ⟨t, fun σ => ?_⟩
  change σ • t / t = f.1 σ * (σ • t / t) / f.1 σ
  rw [mul_comm, mul_div_cancel_right]

variable [IsGalois K Ω]

theorem exists_fieldKummer_matching_level
    (f : continuousCocycles (K := K) (Ω := Ω) p) (n : ℕ) :
    ∃ (a : Kˣ) (g : continuousCocycles (K := K) (Ω := Ω) p),
      Rational.classOfCocycle p g = (Rational.kummerHom (Ω := Ω) p a).toAdd ∧
        ∀ σ : Ω ≃ₐ[K] Ω, (g.1 σ).1 n = (f.1 σ).1 n := by
  obtain ⟨a, b, ha, hb, hbf⟩ := finiteLevel_field_source p f n
  let R := rootTower (Ω := Ω) p (Fact.out : p.Prime).pos a
  let q : Ωˣ := Units.mk0 (R.root n) (R.root_ne_zero (Fact.out : p.Prime).pos ha n)
  let z : Ωˣ := b / q
  have hq : (q : Ω) ^ (p ^ n) = algebraMap K Ω a := R.root_pow_eq n
  have hz : z ^ (p ^ n) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have hzv : (z : Ω) = (b : Ω) / (q : Ω) := Units.val_div_eq_div_val _ _
    rw [hzv, div_pow, hb, hq, div_self ((map_ne_zero (algebraMap K Ω)).mpr ha)]
  obtain ⟨t, ht⟩ := exists_tate_with_level p n z hz
  let c := R.continuousCocycleValue (Fact.out : p.Prime).pos ha
  let g := adjustCocycle p c t
  refine ⟨Units.mk0 a ha, g, ?_, fun σ => ?_⟩
  · have hc := congrArg (Rational.standardMap (K := K) (Ω := Ω) p) (adjustCocycle_class p c t)
    rw [Rational.standardMap_classOfCocycle, Rational.standardMap_classOfCocycle] at hc
    exact hc
  · change (c.1 σ).1 n * (σ • t.1 n / t.1 n) = (f.1 σ).1 n
    rw [ht]
    apply Units.ext
    rw [Units.val_mul, Units.val_div_eq_div_val]
    have hsz : ((σ • z : Ωˣ) : Ω) = σ (z : Ω) := rfl
    have hzv : (z : Ω) = (b : Ω) / (q : Ω) := Units.val_div_eq_div_val _ _
    rw [hsz, hzv, map_div₀, ← hbf σ]
    change (σ (q : Ω) / (q : Ω)) *
      ((σ (b : Ω) / σ (q : Ω)) / ((b : Ω) / (q : Ω))) = σ (b : Ω) / (b : Ω)
    have hsq : σ (q : Ω) ≠ 0 := by simpa only [map_zero] using σ.injective.ne q.ne_zero
    field_simp [q.ne_zero, b.ne_zero, hsq]
    <;> ring

theorem exists_fieldKummer_coordinate_approximation
    (f : continuousCocycles (K := K) (Ω := Ω) p) (n : ℕ) :
    ∃ (a : Kˣ) (g : continuousCocycles (K := K) (Ω := Ω) p),
      Rational.classOfCocycle p g = (Rational.kummerHom (Ω := Ω) p a).toAdd ∧
        ∀ σ : Ω ≃ₐ[K] Ω,
          ‖Rational.coefficientMap p (Additive.ofMul (g.1 σ)) -
            Rational.coefficientMap p (Additive.ofMul (f.1 σ))‖ ≤ ‖(p : ℚ_[p])‖ ^ n := by
  obtain ⟨a, g, hg, hn⟩ := exists_fieldKummer_matching_level p f n
  exact ⟨a, g, hg, fun σ =>
    Rational.norm_coefficientMap_sub_le_prime_pow_of_level_eq p _ _ n (hn σ)⟩

end
end JoshiTeich.Act1Scene1.LocalKummer
