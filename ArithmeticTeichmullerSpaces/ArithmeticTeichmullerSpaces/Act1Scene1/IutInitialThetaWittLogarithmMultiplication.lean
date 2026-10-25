import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittIwasawaLimit

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-LOGARITHM-MULTIPLICATION
source: Joshi II multiplicative-formal-group Tate logarithm in
`eq:tate-module-of-lubin-tate` and `pr:teichmuller-lift-A/B`.
fidelity: the coordinate product x+y+xy remains in the actual all-radius
log convergence domain. The normalized p-power quotient of a product
is the sum of the quotients plus p^k times their product. Continuity
makes this error tend to zero, proving the logarithmic product law
for the existing convergent logarithm. Original proofs; no code copied.
boundary: Scene1/Derived; paper B/period/BK identities and nonvanishing
remain separate obligations. No logarithmic product law is an input.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittLogarithmMultiplication

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusPadicScalars InitialThetaWittLogarithmSeries
open InitialThetaWittIwasawaLimit
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def InDomain (x : Carrier D w) : Prop :=
  ∀ ρ : Radius, InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ x < 1

theorem inDomain_mul_coordinate (x y : Carrier D w) (hx : InDomain D w x) (hy : InDomain D w y) :
    InDomain D w (x + y + x * y) := by
  intro ρ
  change ‖InitialThetaWittAllRadiusCompletion.evaluate D w ρ (x + y + x * y)‖ < 1
  simp only [map_add, map_mul]
  apply (InitialThetaWittRhoUltrametric.norm_add_le_max D w ρ _ _).trans_lt
  apply max_lt
  · exact (InitialThetaWittRhoUltrametric.norm_add_le_max D w ρ _ _).trans_lt (max_lt (hx ρ) (hy ρ))
  · exact (norm_mul_le _ _).trans_lt
      (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hx ρ) (hy ρ).le)

theorem quotient_mul_coordinate (x y : Carrier D w) (k : ℕ) :
    quotient D w (x + y + x * y) k = quotient D w x k + quotient D w y k +
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) •
        (quotient D w x k * quotient D w y k) := by
  let p := Arithmetic.residueChar w.1
  let a : Carrier D w := commonPadicMap D w ((p : Padic p) ^ k)
  let b : Carrier D w := commonPadicMap D w (((p : Padic p) ^ k)⁻¹)
  have hp : (p : Padic p) ^ k ≠ 0 := pow_ne_zero k (Nat.cast_ne_zero.mpr
    (Arithmetic.residueChar_prime w.1).ne_zero)
  have hab : a * b = 1 := by
    change commonPadicMap D w _ * commonPadicMap D w _ = 1
    rw [← map_mul, mul_inv_cancel₀ hp, map_one]
  have he : (1 + (x + y + x * y)) ^ (p ^ k) = (1 + x) ^ (p ^ k) * (1 + y) ^ (p ^ k) := by
    rw [show 1 + (x + y + x * y) = (1 + x) * (1 + y) by ring, mul_pow]
  simp only [quotient, Algebra.smul_def]
  change b * ((1 + (x + y + x * y)) ^ (p ^ k) - 1) =
    b * ((1 + x) ^ (p ^ k) - 1) + b * ((1 + y) ^ (p ^ k) - 1) +
      a * ((b * ((1 + x) ^ (p ^ k) - 1)) * (b * ((1 + y) ^ (p ^ k) - 1)))
  rw [he]
  linear_combination -(b * ((1 + x) ^ (p ^ k) - 1) * ((1 + y) ^ (p ^ k) - 1)) * hab

theorem tendsto_product_error (x y : Carrier D w) (hx : InDomain D w x) (hy : InDomain D w y) :
    Filter.Tendsto
      (fun k : ℕ => ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) •
        (quotient D w x k * quotient D w y k)) Filter.atTop (𝓝 0) := by
  have hp : Filter.Tendsto (fun k : ℕ =>
      (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := Arithmetic.residueChar w.1))
  simpa only [zero_smul] using hp.smul ((tendsto_quotient D w x hx).mul (tendsto_quotient D w y hy))

theorem logOneAdd_mul_coordinate (x y : Carrier D w) (hx : InDomain D w x) (hy : InDomain D w y) :
    logOneAdd D w (x + y + x * y) = logOneAdd D w x + logOneAdd D w y := by
  have h := ((tendsto_quotient D w x hx).add (tendsto_quotient D w y hy)).add
    (tendsto_product_error D w x y hx hy)
  have he : quotient D w (x + y + x * y) = fun k =>
      quotient D w x k + quotient D w y k +
        ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) •
          (quotient D w x k * quotient D w y k) := funext (quotient_mul_coordinate D w x y)
  apply tendsto_nhds_unique (tendsto_quotient D w _ (inDomain_mul_coordinate D w x y hx hy))
  rw [he]
  simpa only [add_zero] using h

end
end JoshiTeich.Act1Scene1.InitialThetaWittLogarithmMultiplication
