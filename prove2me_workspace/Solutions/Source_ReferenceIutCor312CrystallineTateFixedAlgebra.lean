import Solutions.Source_ReferenceIutCor312CrystallineTateFrobeniusFixed

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

noncomputable section

private def algebraOfSubringMap {S A : Type*} [CommSemiring S] [CommRing A] (R : Subring A)
    (f : S →+* ↥R) : Algebra S ↥R :=
  RingHom.toAlgebra' f (fun a x => mul_comm (f a) x)

private theorem algebraMap_algebraOfSubringMap {S A : Type*} [CommSemiring S] [CommRing A]
    (R : Subring A) (f : S →+* ↥R) :
    @algebraMap S ↥R _ _ (algebraOfSubringMap R f) = f :=
  rfl

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable {Ω : Type*} [Field Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (j : Ω →+* C)

local notation "Bₜ" => ACrisInvertTatePeriod C p j
local notation "F" => ACrisInvertTatePeriodFrobeniusFixed C p j

/-- The Frobenius-fixed ring is a rational p-adic algebra via its restricted scalar map. -/
instance instAlgebraPadicCrystallineTateFixed : Algebra (Padic p) ↥F :=
  algebraOfSubringMap (A := Bₜ) F (padicMapACrisInvertTatePeriodFrobeniusFixed C p j)

theorem algebraMap_ACrisInvertTatePeriodFrobeniusFixed :
    (algebraMap (Padic p) ↥F : Padic p →+* ↥F) =
      padicMapACrisInvertTatePeriodFrobeniusFixed C p j :=
  algebraMap_algebraOfSubringMap (A := Bₜ) F (padicMapACrisInvertTatePeriodFrobeniusFixed C p j)

theorem coe_algebraMap_ACrisInvertTatePeriodFrobeniusFixed (a : Padic p) :
    (algebraMap (Padic p) ↥F a : Bₜ) = padicMapACrisInvertTatePeriod C p j a :=
  (congrArg (fun f : Padic p →+* ↥F => (f a : Bₜ))
    (algebraMap_ACrisInvertTatePeriodFrobeniusFixed C p j)).trans
    (coe_padicMapACrisInvertTatePeriodFrobeniusFixed C p j a)

theorem smul_ACrisInvertTatePeriodFrobeniusFixed (a : Padic p) (z : ↥F) :
    a • z = padicMapACrisInvertTatePeriodFrobeniusFixed C p j a * z :=
  (Algebra.smul_def a z).trans
    (congrArg (fun f : Padic p →+* ↥F => f a * z)
      (algebraMap_ACrisInvertTatePeriodFrobeniusFixed C p j))

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
