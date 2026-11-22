import Solutions.Source_ReferenceIutCor312FontaineGalois
import Solutions.Source_ReferenceIutCor312KummerPreTiltGalois

/-!
For the Kummer tower of Joshi III §9.6, the Witt Galois image of its
Teichmüller lift is the product of the Teichmüller lifts of its
Kummer cocycle and the original tower.
-/

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.LocalKummer.RootTower

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] {a : K}

local notation "Ω₀" => CompletedAlgebraicClosure.Algebraic K
local notation "C" => CompletedAlgebraicClosure.Field K
local notation "ι" => (UniformSpace.Completion.coeRingHom : Ω₀ →+* C)

variable [Fact (0 < ‖(p : CompletedAlgebraicClosure.Field K)‖ ∧
  ‖(p : CompletedAlgebraicClosure.Field K)‖ < 1)]

/-- The Galois image of the original Teichmüller lift differs by the
Teichmüller lift of its Kummer cocycle in the same Witt ring. -/
theorem extendGaloisFontaine_teichmuller_toGeometricPreTilt
    (R : RootTower (Ω := CompletedAlgebraicClosure.Algebraic K) p a)
    (ha : ‖(algebraMap K C a)‖ ≤ 1) (hne : a ≠ 0) (σ : Ω₀ ≃ₐ[K] Ω₀) :
    CompletedAlgebraicClosure.extendGaloisFontaine p σ
      (WittVector.teichmuller p (R.toGeometricPreTilt ι ha)) =
      WittVector.teichmuller p (CyclotomicTateTilt.toPreTilt C p (R.mapKummerCocycle ι hne σ)) *
        WittVector.teichmuller p (R.toGeometricPreTilt ι ha) := by
  rw [CompletedAlgebraicClosure.extendGaloisFontaine_teichmuller,
    R.extendGaloisPreTilt_toGeometricPreTilt ha hne σ]
  exact map_mul (WittVector.teichmuller p) _ _

end

end JoshiTeich.Act1Scene1.LocalKummer.RootTower
