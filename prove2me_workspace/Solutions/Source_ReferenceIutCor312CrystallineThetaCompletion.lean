import Solutions.Source_ReferenceIutCor312CrystallineTheta
import Mathlib.RingTheory.AdicCompletion.RingHom

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [CharZero C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "𝒪" => (LocalGeometricFontaine.integerRing C)
local notation "θ" => (Perfectoid.thetaMap (O := 𝒪) (p := p))
local notation "I" => (Ideal.span {(p : A0 C p)} : Ideal (A0 C p))
local notation "J" => (Ideal.span {(p : 𝒪)} : Ideal 𝒪)

private theorem thetaA0_adicPow_le_comap (n : ℕ) :
    I ^ n ≤ (J ^ n).comap (thetaA0 C p) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]

private def thetaQuotient (n : ℕ) : (A0 C p) ⧸ I ^ n →+* 𝒪 ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) (thetaA0 C p) (thetaA0_adicPow_le_comap C p n)

private theorem thetaQuotient_mk (n : ℕ) (x : A0 C p) :
    thetaQuotient C p n (Ideal.Quotient.mk (I ^ n) x) =
      Ideal.Quotient.mk (J ^ n) (thetaA0 C p x) :=
  Ideal.quotientMap_mk

private def thetaCrystallineResidue (n : ℕ) : ACris C p →+* 𝒪 ⧸ J ^ n :=
  (thetaQuotient C p n).comp (AdicCompletion.evalₐ I n).toRingHom

private theorem thetaCrystallineResidue_compatible {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow J hmn).comp (thetaCrystallineResidue C p n) =
      thetaCrystallineResidue C p m := by
  apply RingHom.ext
  intro z
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I (A0 C p) z
  change Ideal.Quotient.factorPow J hmn
    (thetaQuotient C p n (AdicCompletion.evalₐ I n (AdicCompletion.mk I (A0 C p) s))) =
      thetaQuotient C p m (AdicCompletion.evalₐ I m (AdicCompletion.mk I (A0 C p) s))
  simp only [AdicCompletion.evalₐ_mk, thetaQuotient_mk, Ideal.Quotient.factor_mk]
  rw [← thetaQuotient_mk C p m (s.val n), ← thetaQuotient_mk C p m (s.val m)]
  exact congrArg (thetaQuotient C p m) (AdicCompletion.Ideal.mk_eq_mk I hmn s)

/-- Extend the Fontaine map on A0 to its p-adic completion. -/
def thetaCrystalline : ACris C p →+* 𝒪 :=
  IsAdicComplete.liftRingHom J (thetaCrystallineResidue C p)
    (thetaCrystallineResidue_compatible C p)

/-- Apply the uncompleted Fontaine map to any representative of the given residue. -/
theorem eval_thetaCrystalline_of_eq (n : ℕ) (z : ACris C p) (x : A0 C p)
    (hx : AdicCompletion.evalₐ I n z = Ideal.Quotient.mk (I ^ n) x) :
    Ideal.Quotient.mk (J ^ n) (thetaCrystalline C p z) =
      Ideal.Quotient.mk (J ^ n) (thetaA0 C p x) := by
  unfold thetaCrystalline
  rw [IsAdicComplete.mk_liftRingHom]
  change thetaQuotient C p n (AdicCompletion.evalₐ I n z) = _
  rw [hx, thetaQuotient_mk]

theorem thetaCrystalline_comp_algebraMap :
    (thetaCrystalline C p).comp (algebraMap (A0 C p) (ACris C p)) = thetaA0 C p := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' J
  intro n x
  exact eval_thetaCrystalline_of_eq C p n _ x (AdicCompletion.evalₐ_of I n x)

/-- The crystalline logarithm specializes modulo p^k through any sufficiently long sum. -/
theorem eval_thetaCrystalline_logOfMemKerSupPrime (x : Ainf C p)
    (hx : x ∈ RingHom.ker θ ⊔ Ideal.span {(p : Ainf C p)})
    {k N : ℕ} (hN : p * k ≤ N) :
    Ideal.Quotient.mk (J ^ k) (thetaCrystalline C p (logOfMemKerSupPrime C p x hx)) =
      Ideal.Quotient.mk (J ^ k)
        (thetaA0 C p (DividedPowerLog.logPartialSum (fun m => gammaInOfMemKerSupPrime C p m x hx) N)) :=
  eval_thetaCrystalline_of_eq C p k _ _ (eval_logOfMemKerSupPrime C p x hx hN)

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
