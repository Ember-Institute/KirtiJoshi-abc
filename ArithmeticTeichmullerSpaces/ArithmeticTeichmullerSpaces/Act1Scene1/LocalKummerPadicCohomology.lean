import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerPadicModule
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerMathlibCohomology

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-PADIC-COHOMOLOGY
source: Joshi III Z_p(1)-valued Kummer classes (3190--3208).
fidelity: constructs the continuous Z_p-linear Tate representation and the
standard continuous H1 class of the existing Kummer cocycle. Coboundaries
give equal classes. This does not construct H^1_e or rational coefficients.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer
open scoped Topology
universe u v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] (p : ℕ) [Fact p.Prime]

def padicTateRepresentation :
    ContRepresentation ℤ_[p] (Ω ≃ₐ[K] Ω) (Additive (cyclotomicTateGroup p Ω)) where
  toMonoidHom.toFun σ := {
    toFun x := (tateRepresentation (K := K) p σ) x
    map_add' := (tateRepresentation (K := K) p σ).map_add
    map_smul' r x := by
      change Additive.ofMul (σ • padicPower r x.toMul) =
        Additive.ofMul (padicPower r (σ • x.toMul))
      rw [tateAction_padicPower]
    cont := (tateRepresentation (K := K) p σ).continuous
  }
  toMonoidHom.map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    change (tateRepresentation (K := K) p (1 : Ω ≃ₐ[K] Ω)) x = x
    rw [map_one]
    rfl
  toMonoidHom.map_mul' σ τ := by
    apply ContinuousLinearMap.ext
    intro x
    change (tateRepresentation (K := K) p (σ * τ)) x =
      (tateRepresentation (K := K) p σ) ((tateRepresentation (K := K) p τ) x)
    rw [map_mul]
    rfl

def padicTateTopRep : TopRep ℤ_[p] (Ω ≃ₐ[K] Ω) := TopRep.of (padicTateRepresentation p)

def padicAdditiveCocycle (f : continuousCocycles (K := K) (Ω := Ω) p) :
    C((Ω ≃ₐ[K] Ω), padicTateTopRep (K := K) (Ω := Ω) p) :=
  ⟨fun σ => Additive.ofMul (f.1 σ), continuous_ofMul.comp f.1.continuous⟩

theorem padicAdditiveCocycle_law (f : continuousCocycles (K := K) (Ω := Ω) p)
    (σ τ : Ω ≃ₐ[K] Ω) :
    padicAdditiveCocycle p f (σ * τ) =
      (padicTateTopRep p).ρ σ (padicAdditiveCocycle p f τ) + padicAdditiveCocycle p f σ :=
  congrArg Additive.ofMul (f.2 σ τ)

def padicClassOfCocycle (f : continuousCocycles (K := K) (Ω := Ω) p) :
    continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p) :=
  ContinuousH1Homogeneous.classOf _ (padicAdditiveCocycle p f) (padicAdditiveCocycle_law p f)

theorem padicClassOfCocycle_eq (f g : continuousCocycles (K := K) (Ω := Ω) p)
    (hfg : groupCohomology.IsMulCoboundary₁ (fun σ => g.1 σ / f.1 σ)) :
    padicClassOfCocycle p f = padicClassOfCocycle p g := by
  obtain ⟨t, ht⟩ := hfg
  apply ContinuousH1Homogeneous.classOf_eq_of_coboundary _ _ _
    (padicAdditiveCocycle_law p f) (padicAdditiveCocycle_law p g) (Additive.ofMul t)
  · change Continuous (fun σ : Ω ≃ₐ[K] Ω => Additive.ofMul (σ • t))
    exact continuous_ofMul.comp ((continuous_tateAction p).comp
      (show Continuous (fun σ : Ω ≃ₐ[K] Ω => (σ, t)) from
        continuous_id.prodMk continuous_const))
  · intro σ
    exact congrArg Additive.ofMul (ht σ).symm

def toPadicH1 : continuousH1 (K := K) (Ω := Ω) p →
    continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p) :=
  Quotient.lift (padicClassOfCocycle p) (fun f g h => padicClassOfCocycle_eq p f g h)

theorem toPadicH1_class (f : continuousCocycles (K := K) (Ω := Ω) p) :
    toPadicH1 p (continuousH1Class f) = padicClassOfCocycle p f := rfl

end
end JoshiTeich.Act1Scene1.LocalKummer
