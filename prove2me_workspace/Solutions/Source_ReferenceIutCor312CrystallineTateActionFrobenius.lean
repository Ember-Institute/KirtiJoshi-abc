import Solutions.Source_ReferenceIutCor312CrystallineTateAction
import Solutions.Source_ReferenceIutCor312CrystallineTateFrobenius

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open CrystallineEnvelope

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "Ω₀" => Algebraic K
local notation "C" => Field K
local notation "G" => (Ω₀ ≃ₐ[K] Ω₀)
local notation "ι" => (UniformSpace.Completion.coeRingHom : Ω₀ →+* C)
local notation "B" => ACrisInvertP C p
local notation "Bₜ" => ACrisInvertTatePeriod C p ι
local notation "t" => mappedTateBasisPeriod C p ι
local notation "j" => algebraMap B Bₜ
local notation "φ" => frobeniusACrisInvertTatePeriod C p ι

/-- The original Galois action commutes with crystalline Frobenius after
inverting the prime and the original Tate period. -/
theorem extendGaloisACrisInvertTatePeriod_frobenius (σ : G) (z : Bₜ) :
    extendGaloisACrisInvertTatePeriod p σ (φ z) =
      φ (extendGaloisACrisInvertTatePeriod p σ z) := by
  let g : Bₜ →+* Bₜ := extendGaloisACrisInvertTatePeriodHom p σ
  let gₚ : B →+* B := mapACrisInvertP C p (extendGaloisACris p σ)
  let φₚ : B →+* B := mapACrisInvertP C p (frobeniusACris C p)
  have h : g.comp φ = RingHom.comp φ g := by
    refine IsLocalization.ringHom_ext (Submonoid.powers t) (RingHom.ext fun x => ?_)
    change g (φ (j x)) = φ (g (j x))
    calc
      g (φ (j x)) = g (j (φₚ x)) :=
        congrArg g (frobeniusACrisInvertTatePeriod_algebraMap C p ι x)
      _ = j (gₚ (φₚ x)) :=
        extendGaloisACrisInvertTatePeriodHom_algebraMap p σ (φₚ x)
      _ = j (φₚ (gₚ x)) :=
        congrArg (j : B →+* Bₜ) (extendGaloisACrisInvertP_frobenius p σ x)
      _ = φ (j (gₚ x)) :=
        (frobeniusACrisInvertTatePeriod_algebraMap C p ι (gₚ x)).symm
      _ = φ (g (j x)) :=
        congrArg φ (extendGaloisACrisInvertTatePeriodHom_algebraMap p σ x).symm
  change g (φ z) = φ (g z)
  exact RingHom.congr_fun h z

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
