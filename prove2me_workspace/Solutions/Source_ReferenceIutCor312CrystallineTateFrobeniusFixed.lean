import Solutions.Source_ReferenceIutCor312CrystallineTatePadicScalars
import Mathlib.Algebra.Ring.Subring.Basic

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable {Ω : Type*} [Field Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (j : Ω →+* C)

local notation "Bₜ" => ACrisInvertTatePeriod C p j
local notation "φ" => frobeniusACrisInvertTatePeriod C p j

/-- The subring fixed by crystalline Frobenius after inverting the prime and
the original Tate period. -/
def ACrisInvertTatePeriodFrobeniusFixed : Subring Bₜ :=
  RingHom.eqLocus φ (RingHom.id Bₜ)

@[simp]
theorem mem_ACrisInvertTatePeriodFrobeniusFixed (z : Bₜ) :
    z ∈ ACrisInvertTatePeriodFrobeniusFixed C p j ↔ φ z = z :=
  Iff.rfl

/-- The rational p-adic scalar map with codomain restricted to the
Frobenius-fixed subring. -/
def padicMapACrisInvertTatePeriodFrobeniusFixed :
    Padic p →+* ACrisInvertTatePeriodFrobeniusFixed C p j :=
  (padicMapACrisInvertTatePeriod C p j).codRestrict
    (ACrisInvertTatePeriodFrobeniusFixed C p j) fun a =>
      (mem_ACrisInvertTatePeriodFrobeniusFixed C p j _).2
        (frobeniusACrisInvertTatePeriod_padicMap C p j a)

@[simp]
theorem coe_padicMapACrisInvertTatePeriodFrobeniusFixed (a : Padic p) :
    (padicMapACrisInvertTatePeriodFrobeniusFixed C p j a : Bₜ) =
      padicMapACrisInvertTatePeriod C p j a :=
  rfl

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
