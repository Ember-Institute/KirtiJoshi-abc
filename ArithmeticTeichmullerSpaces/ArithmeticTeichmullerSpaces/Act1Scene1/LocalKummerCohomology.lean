import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerContinuity

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-COHOMOLOGY
source: Joshi III compatible roots and the resulting Kummer class (3190--3208).
fidelity: forms the quotient of continuous multiplicative cocycles by
coboundaries. Any two root towers of the same nonzero element give the same
class. The quotient has no supplied topology or Z_p-module structure.
H^1_e membership and the Bloch--Kato comparison remain open.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]

/-- Continuous cocycles for the Krull Galois group and inverse-limit coefficients. -/
def continuousCocycles (p : ℕ) :=
  {f : C((Ω ≃ₐ[K] Ω), cyclotomicTateGroup p Ω) // groupCohomology.IsMulCocycle₁ f}

/-- Two continuous cocycles differ by a multiplicative coboundary. -/
def continuousCocycleSetoid (p : ℕ) : Setoid (continuousCocycles (K := K) (Ω := Ω) p) where
  r f g := groupCohomology.IsMulCoboundary₁ (fun σ => g.1 σ / f.1 σ)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro f
      exact ⟨1, fun σ => by simp⟩
    · intro f g h
      obtain ⟨t, ht⟩ := h
      refine ⟨t⁻¹, fun σ => ?_⟩
      simpa only [smul_inv', inv_div_inv, inv_div] using congrArg Inv.inv (ht σ)
    · intro f g h hfg hgh
      obtain ⟨t, ht⟩ := hfg
      obtain ⟨s, hs⟩ := hgh
      refine ⟨s * t, fun σ => ?_⟩
      rw [smul_mul', mul_div_mul_comm, hs σ, ht σ, div_mul_div_cancel]

/-- Degree-one continuous cohomology as a set of cocycles modulo coboundaries. -/
def continuousH1 (p : ℕ) := Quotient (continuousCocycleSetoid (K := K) (Ω := Ω) p)

def continuousH1Class {p : ℕ} (f : continuousCocycles (K := K) (Ω := Ω) p) :
    continuousH1 (K := K) (Ω := Ω) p :=
  Quotient.mk (continuousCocycleSetoid p) f

theorem continuousH1Class_eq_iff {p : ℕ}
    (f g : continuousCocycles (K := K) (Ω := Ω) p) :
    continuousH1Class f = continuousH1Class g ↔
      groupCohomology.IsMulCoboundary₁ (fun σ => g.1 σ / f.1 σ) :=
  Quotient.eq

namespace RootTower
variable {p : ℕ} {a : K} (R S : RootTower (Ω := Ω) p a) (hp : 0 < p) (ha : a ≠ 0)

/-- The coordinate ratio S/R is one compatible system of roots of unity. -/
def rootChange : cyclotomicTateGroup p Ω :=
  ⟨fun n => Units.mk0 (S.root n / R.root n)
    (div_ne_zero (S.root_ne_zero hp ha n) (R.root_ne_zero hp ha n)), by
    constructor
    · intro n
      apply Units.ext
      change (S.root n / R.root n) ^ (p ^ n) = 1
      rw [div_pow, S.root_pow_eq, R.root_pow_eq,
        div_self ((map_ne_zero (algebraMap K Ω)).mpr ha)]
    · intro n
      apply Units.ext
      change (S.root (n + 1) / R.root (n + 1)) ^ p = S.root n / R.root n
      rw [div_pow, S.root_succ, R.root_succ]⟩

theorem rootChange_apply (n : ℕ) :
    ((R.rootChange S hp ha).1 n : Ω) = S.root n / R.root n := rfl

theorem kummerCocycle_div_eq (σ : Ω ≃ₐ[K] Ω) :
    S.kummerCocycle hp ha σ / R.kummerCocycle hp ha σ =
      σ • R.rootChange S hp ha / R.rootChange S hp ha := by
  apply Subtype.ext
  funext n
  apply Units.ext
  simp only [Subgroup.coe_div, Pi.div_apply, Units.val_div_eq_div_val]
  change (σ (S.root n) / S.root n) / (σ (R.root n) / R.root n) =
    σ (S.root n / R.root n) / (S.root n / R.root n)
  have hR := R.root_ne_zero hp ha n
  have hS := S.root_ne_zero hp ha n
  have hσR : σ (R.root n) ≠ 0 := by simpa only [map_zero] using σ.injective.ne hR
  rw [map_div₀]
  field_simp [hR, hS, hσR] <;> ring

theorem isMulCoboundary_kummerCocycle_div :
    groupCohomology.IsMulCoboundary₁
      (fun σ => S.kummerCocycle hp ha σ / R.kummerCocycle hp ha σ) :=
  ⟨R.rootChange S hp ha, fun σ => (R.kummerCocycle_div_eq S hp ha σ).symm⟩

variable [Algebra.IsIntegral K Ω]

def continuousCocycleValue : continuousCocycles (K := K) (Ω := Ω) p :=
  ⟨R.continuousCocycle hp ha, R.continuousCocycle_isMulCocycle hp ha⟩

def kummerClass : continuousH1 (K := K) (Ω := Ω) p :=
  continuousH1Class (R.continuousCocycleValue hp ha)

theorem kummerClass_eq : R.kummerClass hp ha = S.kummerClass hp ha :=
  (continuousH1Class_eq_iff _ _).mpr (R.isMulCoboundary_kummerCocycle_div S hp ha)

end RootTower
end
end JoshiTeich.Act1Scene1.LocalKummer
