import ArithmeticTeichmullerSpaces.Act1Scene1.AdicKernelDivision
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTiltFontaine

/-!
source-id: JT-SCENE1-INITIAL-THETA-FONTAINE-KERNEL
source: Joshi II pa:Mochizuki-Ansatz (838), ker(eta_K)=([p-flat]-p);
Mathlib Witt mod-p decomposition and p-adic completeness.
fidelity: proves the exact principal kernel for the same actual W(O_F)
and untilt map. Norm comparison gives integral division of the constant
coefficient; actual p-adic iteration produces the full quotient. No kernel
generator, division, closedness or principal-ideal certificate is input.
Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaFontaineKernel

open JoshiTeich.Prologue InitialThetaTiltFontaine
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance primeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w

/-- Perfectness is transported through the proved actual PreTilt integer-ring equivalence. -/
instance integersPerfect : PerfectRing (InitialThetaTiltIntegers.Integers D w)
    (Arithmetic.residueChar w.1) := by
  apply PerfectRing.ofSurjective
  intro x
  obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius
    (R := InitialThetaTiltField.Source D w) (p := Arithmetic.residueChar w.1)).surjective
      ((InitialThetaTiltIntegers.preTiltEquiv D w).symm x)
  refine ⟨InitialThetaTiltIntegers.preTiltEquiv D w y, ?_⟩
  change y ^ Arithmetic.residueChar w.1 = (InitialThetaTiltIntegers.preTiltEquiv D w).symm x at hy
  rw [frobenius_def, ← map_pow, hy, RingEquiv.apply_symm_apply]

/-- The actual p-adic decomposition of a Witt vector in W(O_F). -/
theorem decomposition (a : Ainf D w) : ∃ b : Ainf D w,
    a = WittVector.teichmuller (Arithmetic.residueChar w.1) (a.coeff 0) +
      (Arithmetic.residueChar w.1 : Ainf D w) * b := by
  have hz : (a - WittVector.teichmuller (Arithmetic.residueChar w.1) (a.coeff 0)).coeff 0 = 0 := by
    change WittVector.constantCoeff (a -
      WittVector.teichmuller (Arithmetic.residueChar w.1) (a.coeff 0)) = 0
    rw [map_sub]
    change a.coeff 0 - a.coeff 0 = 0
    exact sub_self _
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr hz)
  refine ⟨b, ?_⟩
  calc
    a = (a - WittVector.teichmuller (Arithmetic.residueChar w.1) (a.coeff 0)) +
      WittVector.teichmuller (Arithmetic.residueChar w.1) (a.coeff 0) := (sub_add_cancel _ _).symm
    _ = _ := by rw [hb]; ring

/-- Vanishing theta forces the constant coefficient to be divisible by p-flat in O_F. -/
theorem constantCoeff_norm_le (a : Ainf D w) (ha : theta D w a = 0) :
    ‖a.coeff 0‖ ≤ ‖(Arithmetic.residueChar w.1 :
      InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ := by
  obtain ⟨b, hb⟩ := decomposition D w a
  have hz : theta D w (WittVector.teichmuller (Arithmetic.residueChar w.1) (a.coeff 0)) +
      (Arithmetic.residueChar w.1 : LocalGeometricFontaine.integerRing
        (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) * theta D w b = 0 := by
    simpa only [map_add, map_mul, map_natCast, ha] using (congrArg (theta D w) hb).symm
  have he := eq_neg_of_add_eq_zero_left hz
  calc
    ‖a.coeff 0‖ = ‖theta D w (WittVector.teichmuller (Arithmetic.residueChar w.1) (a.coeff 0))‖ :=
      (theta_teichmuller_norm D w _).symm
    _ = ‖(Arithmetic.residueChar w.1 : LocalGeometricFontaine.integerRing
      (InitialThetaCanonicalGeometricFontaine.coefficientField D w))‖ * ‖theta D w b‖ := by
        rw [he, norm_neg, norm_mul]
    _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _)
      ((LocalGeometricFontaine.mem_integerRing _ _).mp (theta D w b).property)

theorem constantCoeff_dvd (a : Ainf D w) (ha : theta D w a = 0) :
    integralLift D w (Arithmetic.residueChar w.1) ∣ a.coeff 0 := by
  have hn : ‖a.coeff 0‖ ≤ ‖integralLift D w (Arithmetic.residueChar w.1)‖ := by
    rw [integralLift_norm]
    exact constantCoeff_norm_le D w a ha
  apply (Valuation.integer.integers
    (NormedField.valuation (K := InitialThetaTiltField.Carrier D w))).dvd_of_le
  exact_mod_cast hn

/-- One integral division leaves p times another element of the actual theta kernel. -/
theorem division_step (a : Ainf D w) (ha : theta D w a = 0) :
    ∃ c r : Ainf D w, theta D w r = 0 ∧
      a = primitive D w * c + (Arithmetic.residueChar w.1 : Ainf D w) * r := by
  obtain ⟨b, hb⟩ := decomposition D w a
  obtain ⟨c, hc⟩ := constantCoeff_dvd D w a ha
  let t := WittVector.teichmuller (Arithmetic.residueChar w.1) c
  have he : a = primitive D w * t + (Arithmetic.residueChar w.1 : Ainf D w) * (b + t) := by
    calc
      a = WittVector.teichmuller (Arithmetic.residueChar w.1) (a.coeff 0) +
        (Arithmetic.residueChar w.1 : Ainf D w) * b := hb
      _ = WittVector.teichmuller (Arithmetic.residueChar w.1)
        (integralLift D w (Arithmetic.residueChar w.1)) * t +
          (Arithmetic.residueChar w.1 : Ainf D w) * b := by rw [hc, map_mul]
      _ = _ := by unfold primitive; ring
  have hz : (Arithmetic.residueChar w.1 : LocalGeometricFontaine.integerRing
      (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) * theta D w (b + t) = 0 := by
    have hh := congrArg (theta D w) he
    have hξ : theta D w (primitive D w) = 0 := primitive_mem_kernel D w
    rw [ha, map_add, map_mul, hξ, zero_mul, zero_add, map_mul, map_natCast] at hh
    exact hh.symm
  have hp : (Arithmetic.residueChar w.1 : LocalGeometricFontaine.integerRing
      (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero
  exact ⟨t, b + t, (mul_eq_zero.mp hz).resolve_left hp, he⟩

/-- Exact principal kernel identity, proved in the original Ainf carrier. -/
theorem kernel_eq_span : RingHom.ker (theta D w) = Ideal.span {primitive D w} := by
  apply AdicKernelDivision.eq_span (Arithmetic.residueChar w.1 : Ainf D w) (primitive D w)
    (RingHom.ker (theta D w)) (primitive_mem_kernel D w)
  intro a
  obtain ⟨c, r, hr, he⟩ := division_step D w a a.property
  exact ⟨c, ⟨r, hr⟩, he⟩

theorem mem_kernel_iff_dvd (a : Ainf D w) :
    theta D w a = 0 ↔ primitive D w ∣ a := by
  change a ∈ RingHom.ker (theta D w) ↔ _
  rw [kernel_eq_span, Ideal.mem_span_singleton]

theorem primitive_prime : Prime (primitive D w) := by
  apply (Ideal.span_singleton_prime (primitive_ne_zero D w)).mp
  rw [← kernel_eq_span]
  exact theta_kernel_isPrime D w

/-- The quotient by the actual displayed equation is the same actual untilt integer ring. -/
def quotientPrimitiveEquiv : (Ainf D w ⧸ Ideal.span {primitive D w}) ≃+*
    LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w) :=
  (Ideal.quotEquivOfEq (kernel_eq_span D w).symm).trans (quotientEquiv D w)

theorem quotientPrimitiveEquiv_mk (a : Ainf D w) :
    quotientPrimitiveEquiv D w (Ideal.Quotient.mk _ a) = theta D w a := by
  exact quotientEquiv_mk D w a

end
end JoshiTeich.Act1Scene1.InitialThetaFontaineKernel
