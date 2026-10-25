import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittLogarithmMultiplication
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateFrobeniusEigen

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ADDITIVE-TATE-PERIOD
source: Joshi II `eq:tate-module-of-lubin-tate`, `pr:teichmuller-lift-A/B`
and the additive Tate periods in B^{phi=p}.
fidelity: the original Tate tower logarithm is additive under tower
multiplication. Bundles these same values into an additive homomorphism
and a homomorphism into the Q_p submodule defined by the actual phi=p
equation. Proves power and inverse laws using this homomorphism.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; injectivity, Z_p linearity, full Tate-module
comparison and paper B/period/BK identities remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittAdditiveTatePeriod

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittTateLogarithm
open InitialThetaWittLogarithmMultiplication InitialThetaWittTateFrobeniusEigen
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem coordinate_mul (x y : Tate D w) :
    coordinate D w (x * y) = coordinate D w x + coordinate D w y + coordinate D w x * coordinate D w y := by
  simp only [coordinate, InitialThetaCyclotomicTateTilt.kernelCoordinate_mul, map_add, map_mul]

theorem tateLog_mul (x y : Tate D w) : tateLog D w (x * y) = tateLog D w x + tateLog D w y := by
  unfold tateLog
  rw [coordinate_mul]
  exact logOneAdd_mul_coordinate D w _ _ (coordinate_lt_one D w x) (coordinate_lt_one D w y)

def tateLogHom : Additive (Tate D w) →+ Carrier D w where
  toFun x := tateLog D w x.toMul
  map_zero' := tateLog_one D w
  map_add' x y := tateLog_mul D w x.toMul y.toMul

theorem tateLog_pow (t : Tate D w) (n : ℕ) : tateLog D w (t ^ n) = n • tateLog D w t := by
  have h := (tateLogHom D w).map_nsmul n (Additive.ofMul t)
  change tateLog D w ((n • Additive.ofMul t).toMul) = n • tateLog D w t at h
  simpa only [toMul_nsmul, toMul_ofMul] using h

theorem tateLog_inv (t : Tate D w) : tateLog D w t⁻¹ = -tateLog D w t :=
  map_neg (tateLogHom D w) (Additive.ofMul t)

def frobeniusPrimeSubmodule : Submodule (Padic (Arithmetic.residueChar w.1)) (Carrier D w) where
  carrier := {x | InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x =
    (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • x}
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [map_zero, smul_zero]
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, hx, hy, smul_add]
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [InitialThetaWittAllRadiusPadicScalars.frobenius_smul, hx, smul_comm]

theorem tateLog_mem_frobeniusPrime (t : Tate D w) : tateLog D w t ∈ frobeniusPrimeSubmodule D w :=
  frobenius_tateLog_eq_prime_smul D w t

def tateLogEigenHom : Additive (Tate D w) →+ frobeniusPrimeSubmodule D w where
  toFun x := ⟨tateLogHom D w x, tateLog_mem_frobeniusPrime D w x.toMul⟩
  map_zero' := Subtype.ext (map_zero (tateLogHom D w))
  map_add' x y := Subtype.ext (map_add (tateLogHom D w) x y)

theorem tateLogEigenHom_value (t : Tate D w) :
    (tateLogEigenHom D w (Additive.ofMul t) : Carrier D w) = tateLog D w t := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittAdditiveTatePeriod
