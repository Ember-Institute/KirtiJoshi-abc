import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittIwasawaLimit

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TATE-FROBENIUS-EIGEN
source: Joshi II `eq:tate-module-of-lubin-tate`, `pr:teichmuller-lift-A/B`
and the inclusion of logarithmic Tate periods in B^{phi=p}.
fidelity: the actual normalized p-power Tate coordinates converge to
the previously constructed Tate logarithm. Their shift law proves
log(t^p)=p log(t). Combining with the actual Frobenius transport proves
phi(tateLog(t))=p tateLog(t) in the existing common complete ring.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; nonvanishing, the full Tate-module comparison,
paper B identity and period/BK identities remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTateFrobeniusEigen

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittTateLogarithm
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem coordinate_pow (t : Tate D w) (n : ℕ) :
    coordinate D w (t ^ n) = (1 + coordinate D w t) ^ n - 1 := by
  simp [coordinate, InitialThetaCyclotomicTateTilt.kernelCoordinate, map_pow]

def approximation (t : Tate D w) (k : ℕ) : Carrier D w :=
  ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k)⁻¹ •
    coordinate D w (t ^ (Arithmetic.residueChar w.1 ^ k))

theorem approximation_eq_quotient (t : Tate D w) (k : ℕ) :
    approximation D w t k = InitialThetaWittIwasawaLimit.quotient D w (coordinate D w t) k := by
  rw [approximation, coordinate_pow]
  rfl

theorem tendsto_approximation (t : Tate D w) :
    Filter.Tendsto (approximation D w t) Filter.atTop (𝓝 (tateLog D w t)) := by
  have he : approximation D w t = InitialThetaWittIwasawaLimit.quotient D w (coordinate D w t) :=
    funext (approximation_eq_quotient D w t)
  rw [he, tateLog]
  exact InitialThetaWittIwasawaLimit.tendsto_quotient D w (coordinate D w t) (coordinate_lt_one D w t)

theorem approximation_pow_prime (t : Tate D w) (k : ℕ) :
    approximation D w (t ^ Arithmetic.residueChar w.1) k =
      (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • approximation D w t (k + 1) := by
  let p := Arithmetic.residueChar w.1
  have hp0 : (p : Padic p) ≠ 0 := Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero
  have hs : ((p : Padic p) ^ k)⁻¹ = (p : Padic p) * ((p : Padic p) ^ (k + 1))⁻¹ := by
    rw [pow_succ]
    field_simp
  have ht : (t ^ p) ^ (p ^ k) = t ^ (p ^ (k + 1)) := by
    rw [← pow_mul, pow_succ]
    congr 1
    exact Nat.mul_comm _ _
  change ((p : Padic p) ^ k)⁻¹ • coordinate D w ((t ^ p) ^ (p ^ k)) =
    (p : Padic p) • (((p : Padic p) ^ (k + 1))⁻¹ • coordinate D w (t ^ (p ^ (k + 1))))
  rw [smul_smul, ← hs, ht]

theorem tateLog_pow_prime (t : Tate D w) :
    tateLog D w (t ^ Arithmetic.residueChar w.1) =
      (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • tateLog D w t := by
  have h := ((tendsto_approximation D w t).comp (Filter.tendsto_add_atTop_nat 1)).const_smul
    (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1))
  have he := (tendsto_approximation D w (t ^ Arithmetic.residueChar w.1))
  apply tendsto_nhds_unique he
  simpa only [Function.comp_def, ← approximation_pow_prime] using h

theorem frobenius_tateLog_eq_prime_smul (t : Tate D w) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (tateLog D w t) =
      (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • tateLog D w t := by
  rw [frobenius_tateLog, tateLog_pow_prime]

theorem frobenius_tateLog_eq_prime_mul (t : Tate D w) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (tateLog D w t) =
      (Arithmetic.residueChar w.1 : Carrier D w) * tateLog D w t := by
  rw [frobenius_tateLog_eq_prime_smul, Algebra.smul_def, map_natCast]

theorem tateLog_range_subset_frobenius_prime :
    Set.range (tateLog D w) ⊆ {x : Carrier D w |
      InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x =
        (Arithmetic.residueChar w.1 : Carrier D w) * x} := by
  rintro x ⟨t, rfl⟩
  exact frobenius_tateLog_eq_prime_mul D w t

end
end JoshiTeich.Act1Scene1.InitialThetaWittTateFrobeniusEigen
