import Solutions.Source_ReferenceIutCor312CrystallineFontaineKernel
import ArithmeticTeichmullerSpaces.Act1Scene1.WittTeichmullerExpansion

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue WittTeichmullerExpansion
open scoped NNReal

noncomputable section

private theorem exists_teichmuller_multiple_of_dvd_digits
    {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p]
    (k m : ℕ) (a : R) (w : WittVector p R) (h : ∀ i ≤ k, a ^ m ∣ digits p w i) :
    ∃ v : WittVector p R, (p : WittVector p R) ^ (k + 1) ∣
      w - (WittVector.teichmuller p a) ^ m * v := by
  let c : ℕ → R := fun i => if hi : i ≤ k then Classical.choose (h i hi) else 0
  have hc (i : ℕ) (hi : i ≤ k) : a ^ m * c i = digits p w i := by
    change a ^ m * (if hi' : i ≤ k then Classical.choose (h i hi') else 0) = digits p w i
    exact (congrArg (fun x : R => a ^ m * x) (dif_pos hi)).trans
      (Classical.choose_spec (h i hi)).symm
  refine ⟨partialSum p c k, ?_⟩
  have heq : partialSum p (fun i => a ^ m * c i) k = partialSum p (digits p w) k := by
    unfold partialSum
    refine Finset.sum_congr rfl fun i hi => ?_
    exact congrArg (fun x : R => WittVector.teichmuller p x * (p : WittVector p R) ^ i)
      (hc i (Finset.mem_Iic.mp hi))
  rw [← map_pow (WittVector.teichmuller p) a m, partialSum_teichmuller_mul, heq]
  exact expands_digits p w k

private theorem exists_teichmuller_pow_multiple_of_coeff_bound
    {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p] [PerfectRing R p]
    (k n m : ℕ) (a : R) (w : WittVector p R) (bound : R → Prop)
    (hdepth : m * p ^ k ≤ p ^ n) (hcoeff : ∀ i ≤ k, bound (w.coeff i))
    (hdvd : ∀ i, m * p ^ i ≤ p ^ n → bound (w.coeff i) → a ^ m ∣ digits p w i) :
    ∃ v : WittVector p R, (p : WittVector p R) ^ (k + 1) ∣
      w - (WittVector.teichmuller p a) ^ m * v := by
  refine exists_teichmuller_multiple_of_dvd_digits p k m a w fun i hi => ?_
  have hle := Nat.mul_le_mul_left m (Nat.pow_le_pow_right hp.out.pos hi)
  exact hdvd i (hle.trans hdepth) (hcoeff i hi)

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
variable (p : ℕ) [Fact p.Prime] [hp : Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "S" => GeometricTiltField.Source C p
local notation "F" => GeometricTiltField.FractionField C p
local notation "W" => Ainf C p

private local instance truncationTiltNorm : NormedField F :=
  GeometricTiltNorm.fractionNormedField C p
private local instance truncationTiltUltrametric : IsUltrametricDist F :=
  GeometricTiltNorm.fractionUltrametric C p

private theorem norm_primeTilt : ‖primeTilt C p‖ = ‖(p : C)‖ := by
  rw [GeometricPreTiltCompleteness.norm_eq_valuation, GeometricTiltSharp.sourceValuation_eq_sharp_norm]
  change ‖GeometricTiltSharp.integralSharp C p (primeTilt C p)‖ = ‖(p : C)‖
  rw [primeTilt, GeometricTiltSharp.integralSharp_rootLift, Subring.coe_natCast]

omit [CompleteSpace C] [IsAlgClosed C] in
private theorem preTilt_norm_pow (x : S) (m : ℕ) : ‖x ^ m‖ = ‖x‖ ^ m := by
  simp only [GeometricPreTiltCompleteness.norm_eq_valuation, map_pow, NNReal.coe_pow]

private theorem preTilt_dvd_of_norm_le (x y : S) (hxy : ‖y‖ ≤ ‖x‖) : x ∣ y := by
  let e := GeometricTiltIntegerRing.preTiltEquiv C p
  have hdvd : e x ∣ e y := by
    apply (Valuation.integer.integers (NormedField.valuation (K := F))).dvd_of_le
    change ‖(e y : F)‖₊ ≤ ‖(e x : F)‖₊
    apply NNReal.coe_le_coe.mp
    change ‖(e y : F)‖ ≤ ‖(e x : F)‖
    exact (GeometricTiltIntegerRing.preTiltEquiv_norm C p y).trans_le
      (hxy.trans_eq (GeometricTiltIntegerRing.preTiltEquiv_norm C p x).symm)
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨e.symm q, e.injective ?_⟩
  rw [map_mul, RingEquiv.apply_symm_apply, hq]

private theorem primeTilt_pow_dvd_teichmuller_digit
    (w : W) (i n m : ℕ) (hdepth : m * p ^ i ≤ p ^ n)
    (hcoeff : PreTilt.coeff n (w.coeff i) = 0) :
    primeTilt C p ^ m ∣ digits p w i := by
  apply preTilt_dvd_of_norm_le C p
  rw [preTilt_norm_pow C p (primeTilt C p), norm_primeTilt C p]
  let c : S := digits p w i
  have hc : w.coeff i = c ^ (p ^ i) :=
    (expands_iff_coeff p w (digits p w)).mp (expands_digits p w) i
  apply (pow_le_pow_iff_left₀ (norm_nonneg c) (pow_nonneg (norm_nonneg (p : C)) m)
    (pow_ne_zero i (Fact.out : p.Prime).ne_zero)).mp
  calc
    ‖c‖ ^ (p ^ i) = ‖w.coeff i‖ :=
      (preTilt_norm_pow C p c (p ^ i)).symm.trans
        (congrArg (fun x : S => ‖x‖) hc.symm)
    _ ≤ ‖(p : C)‖ ^ (p ^ n) :=
      (GeometricPreTiltCompleteness.coeff_eq_zero_iff C p (w.coeff i) n).mp hcoeff
    _ ≤ ‖(p : C)‖ ^ (m * p ^ i) := pow_le_pow_of_le_one hp.out.1.le hp.out.2.le hdepth
    _ = (‖(p : C)‖ ^ m) ^ (p ^ i) := pow_mul _ _ _

/-- Vanishing of the first `k + 1` Witt coordinates under a sufficiently
deep pretilt projection gives a multiple of the prescribed power of the
Teichmüller lift of the prime modulo the corresponding prime power. -/
theorem exists_primeTilt_teichmuller_multiple_of_coeff_zero
    (w : W) (k n m : ℕ) (hdepth : m * p ^ k ≤ p ^ n)
    (hcoeff : ∀ i ≤ k, PreTilt.coeff n (w.coeff i) = 0) :
    ∃ v : W, (p : W) ^ (k + 1) ∣
      w - (WittVector.teichmuller p (primeTilt C p)) ^ m * v :=
  exists_teichmuller_pow_multiple_of_coeff_bound (R := S) p k n m (primeTilt C p) w
    (fun x : S => PreTilt.coeff n x = 0) hdepth hcoeff
    (fun i => primeTilt_pow_dvd_teichmuller_digit C p w i n m)

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
