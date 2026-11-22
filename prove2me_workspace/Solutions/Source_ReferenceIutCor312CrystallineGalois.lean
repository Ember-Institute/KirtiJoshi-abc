import Solutions.Source_ReferenceIutCor312CrystallineMaps
import Solutions.Source_ReferenceIutCor312FontaineGalois

/-!
For Joshi III §9.6, the completed Galois automorphisms on the Fontaine
Witt ring induce endomorphisms of the integral divided-power ring and
its p-adic completion.
-/

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open JoshiTeich.Prologue CrystallineEnvelope

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "C" => Field K
local notation "θ" =>
  (Perfectoid.thetaMap (O := LocalGeometricFontaine.integerRing C) (p := p))

theorem extendGaloisFontaine_mem_kerSupPrime (σ : Algebraic K ≃ₐ[K] Algebraic K)
    {x : Ainf C p} (hx : x ∈ kerSupPrime C p) :
    extendGaloisFontaine p σ x ∈ kerSupPrime C p := by
  unfold kerSupPrime at hx ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  refine Submodule.mem_sup.mpr
    ⟨_, (extendGaloisFontaine_mem_thetaKernel_iff p σ a).mpr ha, _, ?_, rfl⟩
  rw [Ideal.mem_span_singleton] at hb ⊢
  simpa only [map_natCast] using map_dvd (extendGaloisFontaine p σ) hb

/-- The Fontaine Galois map on the integral divided-power subalgebra. -/
def extendGaloisA0 (σ : Algebraic K ≃ₐ[K] Algebraic K) : A0 C p →+* A0 C p :=
  mapA0 C p (extendGaloisFontaine p σ).toRingHom fun _ hx =>
    extendGaloisFontaine_mem_kerSupPrime p σ
      ((le_sup_left : RingHom.ker θ ≤ kerSupPrime C p) hx)

@[simp]
theorem extendGaloisA0_algebraMap (σ : Algebraic K ≃ₐ[K] Algebraic K) (x : Ainf C p) :
    extendGaloisA0 p σ (algebraMap (Ainf C p) (A0 C p) x) =
      algebraMap (Ainf C p) (A0 C p) (extendGaloisFontaine p σ x) :=
  mapA0_algebraMap C p (extendGaloisFontaine p σ).toRingHom _ x

/-- The induced Galois endomorphism on the p-adic completion. -/
def extendGaloisACris (σ : Algebraic K ≃ₐ[K] Algebraic K) : ACris C p →+* ACris C p :=
  mapACris C p (extendGaloisA0 p σ)

@[simp]
theorem extendGaloisACris_algebraMap (σ : Algebraic K ≃ₐ[K] Algebraic K) (x : A0 C p) :
    extendGaloisACris p σ (algebraMap (A0 C p) (ACris C p) x) =
      algebraMap (A0 C p) (ACris C p) (extendGaloisA0 p σ x) :=
  mapACris_algebraMap C p (extendGaloisA0 p σ) x

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
