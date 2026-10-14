import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Recognition
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerPadicCohomology

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-H1-EQUIVALENCE
source: continuous cocycles modulo coboundaries and standard integral H1.
fidelity: the existing explicit Tate cocycle quotient maps bijectively to
standard Z_p continuous H1. It also gives an explicit zero-class criterion.
This is not injectivity of integral-to-rational coefficient change.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] (p : ℕ) [Fact p.Prime]

theorem padicClassOfCocycle_eq_iff (f g : continuousCocycles (K := K) (Ω := Ω) p) :
    padicClassOfCocycle p f = padicClassOfCocycle p g ↔
      groupCohomology.IsMulCoboundary₁ (fun σ => g.1 σ / f.1 σ) := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := (ContinuousH1Recognition.classOf_eq_iff (padicTateTopRep p)
      (padicAdditiveCocycle p f) (padicAdditiveCocycle p g)
      (padicAdditiveCocycle_law p f) (padicAdditiveCocycle_law p g)).mp h
    exact ⟨t.toMul, fun σ => congrArg Additive.toMul (ht σ).symm⟩
  · exact padicClassOfCocycle_eq p f g

theorem toPadicH1_injective : Function.Injective (toPadicH1 (K := K) (Ω := Ω) p) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h f =>
    induction b using Quotient.inductionOn with
    | h g => exact Quotient.sound ((padicClassOfCocycle_eq_iff p f g).mp hab)

theorem toPadicH1_surjective : Function.Surjective (toPadicH1 (K := K) (Ω := Ω) p) := by
  intro x
  obtain ⟨f, hf, hfx⟩ := ContinuousH1Recognition.classOf_surjective (padicTateTopRep p) x
  let c : continuousCocycles (K := K) (Ω := Ω) p :=
    ⟨⟨fun σ => (f σ).toMul, continuous_toMul.comp f.continuous⟩,
      fun σ τ => congrArg Additive.toMul (hf σ τ)⟩
  exact ⟨continuousH1Class c, hfx⟩

def padicH1Equiv : continuousH1 (K := K) (Ω := Ω) p ≃
    continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p) :=
  Equiv.ofBijective (toPadicH1 p) ⟨toPadicH1_injective p, toPadicH1_surjective p⟩

theorem padicH1Equiv_apply (c : continuousH1 (K := K) (Ω := Ω) p) :
    padicH1Equiv p c = toPadicH1 p c := rfl

theorem padicClassOfCocycle_eq_zero_iff (f : continuousCocycles (K := K) (Ω := Ω) p) :
    padicClassOfCocycle p f = 0 ↔
      ∃ t : cyclotomicTateGroup p Ω, ∀ σ : Ω ≃ₐ[K] Ω, f.1 σ = σ • t / t := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := (ContinuousH1Recognition.classOf_eq_zero_iff (padicTateTopRep p)
      (padicAdditiveCocycle p f) (padicAdditiveCocycle_law p f)).mp h
    exact ⟨t.toMul, fun σ => congrArg Additive.toMul (ht σ)⟩
  · rintro ⟨t, ht⟩
    apply (ContinuousH1Recognition.classOf_eq_zero_iff (padicTateTopRep p)
      (padicAdditiveCocycle p f) (padicAdditiveCocycle_law p f)).mpr
    exact ⟨Additive.ofMul t, fun σ => congrArg Additive.ofMul (ht σ)⟩

end
end JoshiTeich.Act1Scene1.LocalKummer
