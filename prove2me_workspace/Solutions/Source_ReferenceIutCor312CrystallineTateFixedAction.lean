import Solutions.Source_ReferenceIutCor312CrystallineTateActionFrobenius
import Solutions.Source_ReferenceIutCor312CrystallineTateFixedAlgebra

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open CrystallineEnvelope LocalKummer

noncomputable section

private def restrictAlgebraEquiv {S A : Type*} [CommSemiring S] [CommRing A]
    (R : Subring A) [Algebra S ↥R] (g : RingAut A) (hmem : ∀ x, x ∈ R ↔ g x ∈ R)
    (hscalar : ∀ a : S, g (algebraMap S ↥R a : A) = (algebraMap S ↥R a : A)) :
    ↥R ≃ₐ[S] ↥R :=
  AlgEquiv.ofRingEquiv (f := g.restrict R R hmem) (fun a => Subtype.ext (hscalar a))

private def restrictAlgebraAction {S A G : Type*} [CommSemiring S] [CommRing A] [Monoid G]
    (R : Subring A) [Algebra S ↥R] (g : G →* RingAut A)
    (hmem : ∀ σ x, x ∈ R ↔ g σ x ∈ R)
    (hscalar : ∀ (σ : G) (a : S),
      g σ (algebraMap S ↥R a : A) = (algebraMap S ↥R a : A)) : G →* (↥R ≃ₐ[S] ↥R) where
  toFun σ := restrictAlgebraEquiv R (g σ) (hmem σ) (hscalar σ)
  map_one' := AlgEquiv.ext fun z => Subtype.ext
    (congrArg (fun e : RingAut A => e (z : A)) (map_one g))
  map_mul' σ τ := AlgEquiv.ext fun z => Subtype.ext
    (congrArg (fun e : RingAut A => e (z : A)) (map_mul g σ τ))

private theorem coe_restrictAlgebraAction {S A G : Type*} [CommSemiring S] [CommRing A] [Monoid G]
    (R : Subring A) [Algebra S ↥R] (g : G →* RingAut A)
    (hmem : ∀ σ x, x ∈ R ↔ g σ x ∈ R)
    (hscalar : ∀ (σ : G) (a : S),
      g σ (algebraMap S ↥R a : A) = (algebraMap S ↥R a : A)) (σ : G) (x : ↥R) :
    ((restrictAlgebraAction R g hmem hscalar σ x : ↥R) : A) = g σ x :=
  rfl

private def twistAlgebraAction {S T G : Type*} [CommRing S] [CommRing T] [Algebra S T] [Monoid G]
    (action : G →* (T ≃ₐ[S] T)) (χ : G →* S) : G →* Module.End S T where
  toFun σ := χ σ • (action σ).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro x
    change χ 1 • action 1 x = x
    rw [map_one χ, map_one action, AlgEquiv.one_apply, one_smul]
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    change χ (σ * τ) • action (σ * τ) x = χ σ • action σ (χ τ • action τ x)
    rw [map_mul χ, map_mul action, AlgEquiv.mul_apply, map_smul, mul_smul]

private theorem twistAlgebraAction_algebraMap
    {S T G : Type*} [CommRing S] [CommRing T] [Algebra S T] [Monoid G]
    (action : G →* (T ≃ₐ[S] T)) (χ : G →* S) (σ : G) (a : S) :
    twistAlgebraAction action χ σ (algebraMap S T a) = algebraMap S T (χ σ * a) := by
  change χ σ • action σ (algebraMap S T a) = algebraMap S T (χ σ * a)
  rw [(action σ).commutes, Algebra.smul_def, map_mul]

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "Ω₀" => Algebraic K
local notation "C" => Field K
local notation "G" => (Ω₀ ≃ₐ[K] Ω₀)
local notation "ι" => (UniformSpace.Completion.coeRingHom : Ω₀ →+* C)
local notation "Bₜ" => ACrisInvertTatePeriod C p ι
local notation "F" => ACrisInvertTatePeriodFrobeniusFixed C p ι

private theorem mem_fixed_iff_galois_mem_fixed (σ : G) (z : Bₜ) :
    z ∈ F ↔ extendGaloisACrisInvertTatePeriod p σ z ∈ F := by
  let g : Bₜ ≃+* Bₜ := extendGaloisACrisInvertTatePeriod p σ
  let φ := frobeniusACrisInvertTatePeriod C p ι
  have hcomm : g (φ z) = φ (g z) := extendGaloisACrisInvertTatePeriod_frobenius p σ z
  change z ∈ F ↔ g z ∈ F
  constructor
  · intro hz
    have he : φ z = z := (mem_ACrisInvertTatePeriodFrobeniusFixed C p ι z).1 hz
    exact (mem_ACrisInvertTatePeriodFrobeniusFixed C p ι (g z)).2
      (hcomm.symm.trans (congrArg g he))
  · intro hz
    have he : φ (g z) = g z := (mem_ACrisInvertTatePeriodFrobeniusFixed C p ι (g z)).1 hz
    exact (mem_ACrisInvertTatePeriodFrobeniusFixed C p ι z).2 (g.injective (hcomm.trans he))

private theorem extendGalois_fixed_algebraMap (σ : G) (a : Padic p) :
    extendGaloisACrisInvertTatePeriod p σ (algebraMap (Padic p) ↥F a : Bₜ) =
      (algebraMap (Padic p) ↥F a : Bₜ) :=
  let g : Bₜ ≃+* Bₜ := extendGaloisACrisInvertTatePeriod p σ
  let h := coe_algebraMap_ACrisInvertTatePeriodFrobeniusFixed C p ι a
  (congrArg g h).trans ((extendGaloisACrisInvertTatePeriod_padicMap p σ a).trans h.symm)

/-- The localized Galois action on the Frobenius-fixed ring by p-adic algebra automorphisms. -/
def galoisACrisInvertTatePeriodFrobeniusFixed : G →* (↥F ≃ₐ[Padic p] ↥F) :=
  restrictAlgebraAction (S := Padic p) (A := Bₜ) F (galoisACrisInvertTatePeriod (K := K) p)
    (mem_fixed_iff_galois_mem_fixed p) (extendGalois_fixed_algebraMap p)

@[simp]
theorem coe_galoisACrisInvertTatePeriodFrobeniusFixed (σ : G) (z : ↥F) :
    (galoisACrisInvertTatePeriodFrobeniusFixed p σ z : Bₜ) =
      extendGaloisACrisInvertTatePeriod p σ (z : Bₜ) :=
  coe_restrictAlgebraAction (S := Padic p) (A := Bₜ) F (galoisACrisInvertTatePeriod p)
    (mem_fixed_iff_galois_mem_fixed p) (extendGalois_fixed_algebraMap p) σ z

private def rationalCyclotomicCharacter : G →* Padic p :=
  PadicInt.Coe.ringHom.toMonoidHom.comp
    ((Units.coeHom (PadicInt p)).comp (Cyclotomic.character p))

/-- The cyclotomic twist of the localized Galois action on the Frobenius-fixed ring. -/
def galoisACrisInvertTatePeriodFrobeniusFixedTwist : G →* Module.End (Padic p) ↥F :=
  twistAlgebraAction (galoisACrisInvertTatePeriodFrobeniusFixed p) (rationalCyclotomicCharacter p)

theorem galoisACrisInvertTatePeriodFrobeniusFixedTwist_apply (σ : G) (z : ↥F) :
    galoisACrisInvertTatePeriodFrobeniusFixedTwist p σ z =
      ((Cyclotomic.character p σ : PadicInt p) : Padic p) •
        galoisACrisInvertTatePeriodFrobeniusFixed p σ z :=
  rfl

theorem galoisACrisInvertTatePeriodFrobeniusFixedTwist_scalar (σ : G) (a : Padic p) :
    galoisACrisInvertTatePeriodFrobeniusFixedTwist p σ
        (padicMapACrisInvertTatePeriodFrobeniusFixed C p ι a) =
      padicMapACrisInvertTatePeriodFrobeniusFixed C p ι
        (((Cyclotomic.character p σ : PadicInt p) : Padic p) * a) := by
  let ρ := galoisACrisInvertTatePeriodFrobeniusFixedTwist p
  let χ := rationalCyclotomicCharacter p
  let h := algebraMap_ACrisInvertTatePeriodFrobeniusFixed C p ι
  exact (congrArg (fun z : ↥F => ρ σ z) (RingHom.congr_fun h a).symm).trans
    ((twistAlgebraAction_algebraMap (galoisACrisInvertTatePeriodFrobeniusFixed p) χ σ a).trans
      (RingHom.congr_fun h (χ σ * a)))

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
