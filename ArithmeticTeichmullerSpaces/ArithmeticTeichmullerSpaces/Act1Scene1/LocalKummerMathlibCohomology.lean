import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Homogeneous
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerCohomology

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-MATHLIB-COHOMOLOGY
source: Joshi III local Kummer class (3190--3208); Mathlib continuous cohomology.
fidelity: gives the additive Tate group its continuous Z-linear representation.
The explicit continuous cocycle quotient maps to standard continuous H^1 by
the homogeneous cochain f(h)/f(g). This does not prove H^1_e membership.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω]

def tateRepresentation (p : ℕ) :
    ContRepresentation ℤ (Ω ≃ₐ[K] Ω) (Additive (cyclotomicTateGroup p Ω)) where
  toMonoidHom.toFun σ := {
    toLinearMap := Representation.ofMulDistribMulAction (Ω ≃ₐ[K] Ω)
      (cyclotomicTateGroup p Ω) σ
    cont := by
      change Continuous (fun x : Additive (cyclotomicTateGroup p Ω) =>
        Additive.ofMul (σ • x.toMul))
      exact continuous_ofMul.comp ((continuous_tateAction p).comp
        (show Continuous (fun x : Additive (cyclotomicTateGroup p Ω) => (σ, x.toMul)) from
          continuous_const.prodMk continuous_toMul))
  }
  toMonoidHom.map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    change Additive.ofMul ((1 : Ω ≃ₐ[K] Ω) • x.toMul) = x
    simp
  toMonoidHom.map_mul' σ τ := by
    apply ContinuousLinearMap.ext
    intro x
    change Additive.ofMul ((σ * τ) • x.toMul) = Additive.ofMul (σ • (τ • x.toMul))
    rw [mul_smul]

def tateTopRep (p : ℕ) : TopRep ℤ (Ω ≃ₐ[K] Ω) := TopRep.of (tateRepresentation p)

def additiveCocycle {p : ℕ} (f : continuousCocycles (K := K) (Ω := Ω) p) :
    C((Ω ≃ₐ[K] Ω), tateTopRep (K := K) (Ω := Ω) p) :=
  ⟨fun σ => Additive.ofMul (f.1 σ), continuous_ofMul.comp f.1.continuous⟩

theorem additiveCocycle_law {p : ℕ} (f : continuousCocycles (K := K) (Ω := Ω) p)
    (σ τ : Ω ≃ₐ[K] Ω) :
    additiveCocycle f (σ * τ) =
      (tateTopRep p).ρ σ (additiveCocycle f τ) + additiveCocycle f σ :=
  congrArg Additive.ofMul (f.2 σ τ)

def mathlibClassOfCocycle {p : ℕ} (f : continuousCocycles (K := K) (Ω := Ω) p) :
    continuousCohomology 1 (tateTopRep (K := K) (Ω := Ω) p) :=
  ContinuousH1Homogeneous.classOf _ (additiveCocycle f) (additiveCocycle_law f)

theorem mathlibClassOfCocycle_eq {p : ℕ}
    (f g : continuousCocycles (K := K) (Ω := Ω) p)
    (hfg : groupCohomology.IsMulCoboundary₁ (fun σ => g.1 σ / f.1 σ)) :
    mathlibClassOfCocycle f = mathlibClassOfCocycle g := by
  obtain ⟨t, ht⟩ := hfg
  apply ContinuousH1Homogeneous.classOf_eq_of_coboundary _ _ _
    (additiveCocycle_law f) (additiveCocycle_law g) (Additive.ofMul t)
  · change Continuous (fun σ : Ω ≃ₐ[K] Ω => Additive.ofMul (σ • t))
    exact continuous_ofMul.comp ((continuous_tateAction p).comp
      (show Continuous (fun σ : Ω ≃ₐ[K] Ω => (σ, t)) from
        continuous_id.prodMk continuous_const))
  · intro σ
    exact congrArg Additive.ofMul (ht σ).symm

def toMathlibH1 {p : ℕ} : continuousH1 (K := K) (Ω := Ω) p →
    continuousCohomology 1 (tateTopRep (K := K) (Ω := Ω) p) :=
  Quotient.lift mathlibClassOfCocycle (fun f g h => mathlibClassOfCocycle_eq f g h)

theorem toMathlibH1_class {p : ℕ} (f : continuousCocycles (K := K) (Ω := Ω) p) :
    toMathlibH1 (continuousH1Class f) = mathlibClassOfCocycle f := rfl

end
end JoshiTeich.Act1Scene1.LocalKummer
