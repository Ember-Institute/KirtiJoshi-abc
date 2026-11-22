import Solutions.Source_ReferenceIutCor312CrystallinePadicScalars
import Solutions.Source_ReferenceIutCor312CrystallineTateAction
import Solutions.Source_ReferenceIutCor312CrystallineTateFrobenius

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable {Ω : Type*} [Field Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (j : Ω →+* C)

local notation "B" => ACrisInvertP C p
local notation "Bₜ" => ACrisInvertTatePeriod C p j
local notation "k" => algebraMap B Bₜ

/-- Rational p-adic scalars on the crystalline ring with the original Tate period inverted. -/
def padicMapACrisInvertTatePeriod : Padic p →+* Bₜ :=
  (k : B →+* Bₜ).comp (padicMapACrisInvertP p C)

/-- Localized crystalline Frobenius fixes the image of the rational p-adic scalars. -/
theorem frobeniusACrisInvertTatePeriod_padicMap (a : Padic p) :
    frobeniusACrisInvertTatePeriod C p j (padicMapACrisInvertTatePeriod C p j a) =
      padicMapACrisInvertTatePeriod C p j a :=
  (frobeniusACrisInvertTatePeriod_algebraMap C p j (padicMapACrisInvertP p C a)).trans
    (congrArg (k : B →+* Bₜ)
      (mapACrisInvertP_padicMapACrisInvertP p C (frobeniusACris C p) a))

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open CrystallineEnvelope

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "Ω₀" => Algebraic K
local notation "C" => Field K
local notation "ι" => (UniformSpace.Completion.coeRingHom : Ω₀ →+* C)
local notation "B" => ACrisInvertP C p
local notation "Bₜ" => ACrisInvertTatePeriod C p ι
local notation "k" => algebraMap B Bₜ

/-- The localized Galois action fixes the image of the rational p-adic scalars. -/
theorem extendGaloisACrisInvertTatePeriod_padicMap (σ : Ω₀ ≃ₐ[K] Ω₀) (a : Padic p) :
    extendGaloisACrisInvertTatePeriod p σ (padicMapACrisInvertTatePeriod C p ι a) =
      padicMapACrisInvertTatePeriod C p ι a :=
  (extendGaloisACrisInvertTatePeriod_algebraMap p σ (padicMapACrisInvertP p C a)).trans
    (congrArg (k : B →+* Bₜ)
      (mapACrisInvertP_padicMapACrisInvertP p C (extendGaloisACris p σ) a))

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
