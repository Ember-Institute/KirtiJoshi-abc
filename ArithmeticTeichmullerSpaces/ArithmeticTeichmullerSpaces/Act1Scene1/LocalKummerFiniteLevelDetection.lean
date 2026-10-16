import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerFiniteLevelSource
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerTateBasis

/-!
source-id: JT-SCENE1-INTEGRAL-KUMMER-FINITE-LEVEL-DETECTION
source: the original compact Tate group, its primitive compatible generator,
Cantor intersection and standard integral H1 coboundary recognition.
fidelity: an integral Tate cocycle is a coboundary iff all its finite levels
are coboundaries with roots-of-unity witnesses. Compactness produces one
compatible witness from independently supplied finite-level witnesses.
This proves finite-level zero detection, not inverse-limit surjectivity.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (p : ℕ) [Fact p.Prime]
local notation "T" => cyclotomicTateGroup p Ω

theorem tate_compactSpace : CompactSpace T := by
  letI : CompactSpace (Additive T) := (TateBasis.equiv (p := p) (Ω := Ω)).toHomeomorph.compactSpace
  let e : Additive T ≃ₜ T :=
    { toFun := Additive.toMul
      invFun := Additive.ofMul
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_toMul
      continuous_invFun := continuous_ofMul }
  exact e.compactSpace

theorem exists_tate_with_level (n : ℕ) (z : Ωˣ) (hz : z ^ (p ^ n) = 1) :
    ∃ t : T, t.1 n = z := by
  have hprim := TateBasis.generator_isPrimitive (p := p) (Ω := Ω) n
  obtain ⟨m, _, hm⟩ := hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity _ _).mpr hz)
  exact ⟨TateBasis.generator ^ m, hm⟩

/-- Compatibility is imposed by membership in the original Tate group. -/
def finiteLevelWitnesses (f : continuousCocycles (K := K) (Ω := Ω) p) (n : ℕ) : Set T :=
  {t | ∀ σ : Ω ≃ₐ[K] Ω, (f.1 σ).1 n = (σ • t).1 n / t.1 n}

local instance detectionLevelUnitsTopology : TopologicalSpace Ωˣ := ⊥
local instance detectionLevelUnitsDiscrete : DiscreteTopology Ωˣ := ⟨rfl⟩

theorem finiteLevelWitnesses_isClosed
    (f : continuousCocycles (K := K) (Ω := Ω) p) (n : ℕ) :
    IsClosed (finiteLevelWitnesses p f n) := by
  have heval : Continuous (fun t : T => t.1 n) :=
    (continuous_apply n).comp continuous_induced_dom
  have hs (σ : Ω ≃ₐ[K] Ω) : Continuous (fun t : T => σ • t) := by
    change Continuous (fun t : T => tateAction p σ t)
    exact (continuous_tateAction p).comp
      (show Continuous (fun t : T => (σ, t)) from continuous_const.prodMk continuous_id)
  change IsClosed {t : T | ∀ σ : Ω ≃ₐ[K] Ω, (f.1 σ).1 n = (σ • t).1 n / t.1 n}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun σ => isClosed_eq continuous_const ((heval.comp (hs σ)).div' heval)

theorem finiteLevelWitnesses_decreasing
    (f : continuousCocycles (K := K) (Ω := Ω) p) (n : ℕ) :
    finiteLevelWitnesses p f (n + 1) ⊆ finiteLevelWitnesses p f n := by
  intro t ht σ
  have h := congrArg (fun z : Ωˣ => z ^ p) (ht σ)
  rw [div_pow, (f.1 σ).2.2 n, (σ • t).2.2 n, t.2.2 n] at h
  exact h

theorem padicClass_eq_zero_iff_all_finiteLevels
    (f : continuousCocycles (K := K) (Ω := Ω) p) :
    padicClassOfCocycle p f = 0 ↔
      ∀ n : ℕ, ∃ z : Ωˣ, z ^ (p ^ n) = 1 ∧
        ∀ σ : Ω ≃ₐ[K] Ω, (f.1 σ).1 n = σ • z / z := by
  constructor
  · intro hf
    obtain ⟨t, ht⟩ := (padicClassOfCocycle_eq_zero_iff p f).mp hf
    intro n
    refine ⟨t.1 n, t.2.1 n, fun σ => ?_⟩
    exact congrArg (fun t : T => t.1 n) (ht σ)
  · intro hf
    letI : CompactSpace T := tate_compactSpace p
    have hn (n : ℕ) : (finiteLevelWitnesses p f n).Nonempty := by
      obtain ⟨z, hz, hzf⟩ := hf n
      obtain ⟨t, ht⟩ := exists_tate_with_level p n z hz
      refine ⟨t, fun σ => ?_⟩
      change (f.1 σ).1 n = σ • t.1 n / t.1 n
      rw [ht]
      exact hzf σ
    obtain ⟨t, ht⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (finiteLevelWitnesses p f) (finiteLevelWitnesses_decreasing p f) hn
      (finiteLevelWitnesses_isClosed p f 0).isCompact (finiteLevelWitnesses_isClosed p f)
    apply (padicClassOfCocycle_eq_zero_iff p f).mpr
    refine ⟨t, fun σ => ?_⟩
    apply Subtype.ext
    funext n
    exact Set.mem_iInter.mp ht n σ

end
end JoshiTeich.Act1Scene1.LocalKummer
