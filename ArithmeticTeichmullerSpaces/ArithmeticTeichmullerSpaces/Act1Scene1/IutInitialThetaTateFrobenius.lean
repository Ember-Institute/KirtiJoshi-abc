import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaAdditiveTatePeriod
import Mathlib.RingTheory.WittVector.Frobenius

/-!
source-id: JT-SCENE1-INITIAL-THETA-TATE-FROBENIUS
source: Joshi II B^{phi=p} and the multiplicative-formal-group Tate module
(935--958); the actual principal Fontaine equation (838, 932).
fidelity: applies the original Witt Frobenius to the original Tate
Teichmuller/kernel coordinates. Its n-fold action gives p^n times the
same convergent logarithm after the original Ainf-to-B_dR+ map.
Also computes theta(phi(xi))=p^p-p and proves that this Witt Frobenius
cannot extend continuously to the existing primitive-adic B_dR+.
No Frobenius on the paper's Frechet B or B^{phi=p} identity is assumed.
Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTateFrobenius

open JoshiTeich.Prologue InitialThetaCanonicalGeometricFontaine
open InitialThetaCyclotomicTateTilt
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

/-- The original Witt Frobenius on the original actual Ainf. -/
def phi : InitialThetaTiltFontaine.Ainf D w →+* InitialThetaTiltFontaine.Ainf D w :=
  WittVector.frobenius

theorem phi_teichmuller (a : InitialThetaTiltIntegers.Integers D w) :
    phi D w (WittVector.teichmuller (Arithmetic.residueChar w.1) a) =
      WittVector.teichmuller (Arithmetic.residueChar w.1) (a ^ Arithmetic.residueChar w.1) := by
  rw [phi, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

theorem phi_tateTeichmuller (x : Tate D w) :
    phi D w (teichmuller D w x) = teichmuller D w (x ^ Arithmetic.residueChar w.1) := by
  change phi D w (WittVector.teichmuller (Arithmetic.residueChar w.1) (epsilon D w x)) =
    WittVector.teichmuller (Arithmetic.residueChar w.1) (epsilon D w (x ^ Arithmetic.residueChar w.1))
  rw [phi_teichmuller, map_pow (epsilon D w)]

theorem phi_kernelCoordinate (x : Tate D w) :
    phi D w (kernelCoordinate D w x) = kernelCoordinate D w (x ^ Arithmetic.residueChar w.1) := by
  simp only [kernelCoordinate, map_sub, phi_tateTeichmuller, map_one]

theorem iterate_phi_kernelCoordinate (n : ℕ) (x : Tate D w) :
    (phi D w)^[n] (kernelCoordinate D w x) =
      kernelCoordinate D w (x ^ (Arithmetic.residueChar w.1 ^ n)) := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, pow_one]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, phi_kernelCoordinate, ← pow_mul, ← pow_succ]

def frobeniusCoordinate (n : ℕ) (x : Tate D w) : InitialThetaDeRhamCompletion.Ring D w :=
  InitialThetaDeRhamTeichmuller.ainfToPlus D w ((phi D w)^[n] (kernelCoordinate D w x))

theorem frobeniusCoordinate_eq (n : ℕ) (x : Tate D w) :
    frobeniusCoordinate D w n x =
      InitialThetaDeRhamLogarithm.tateCoordinate D w (x ^ (Arithmetic.residueChar w.1 ^ n)) := by
  rw [frobeniusCoordinate, iterate_phi_kernelCoordinate]
  rfl

theorem theta_frobeniusCoordinate (n : ℕ) (x : Tate D w) :
    InitialThetaDeRhamCompletion.theta D w (frobeniusCoordinate D w n x) = 0 := by
  rw [frobeniusCoordinate_eq]
  exact InitialThetaDeRhamLogarithm.theta_tateCoordinate D w _

def frobeniusLog (n : ℕ) (x : Tate D w) : InitialThetaDeRhamCompletion.Ring D w :=
  InitialThetaDeRhamLogarithm.logOneAdd D w (frobeniusCoordinate D w n x)
    (theta_frobeniusCoordinate D w n x)

theorem frobeniusLog_eq (n : ℕ) (x : Tate D w) :
    frobeniusLog D w n x =
      InitialThetaDeRhamLogarithm.tateLog D w (x ^ (Arithmetic.residueChar w.1 ^ n)) := by
  simp only [frobeniusLog, frobeniusCoordinate_eq, InitialThetaDeRhamLogarithm.tateLog]

theorem tateLog_pow (n : ℕ) (x : Tate D w) :
    InitialThetaDeRhamLogarithm.tateLog D w (x ^ n) =
      n • InitialThetaDeRhamLogarithm.tateLog D w x := by
  have h := (InitialThetaAdditiveTatePeriod.tateLogHom D w).map_nsmul n (Additive.ofMul x)
  change InitialThetaDeRhamLogarithm.tateLog D w ((n • Additive.ofMul x).toMul) =
    n • InitialThetaDeRhamLogarithm.tateLog D w x at h
  simpa only [toMul_nsmul, toMul_ofMul] using h

/-- The actual Witt-Frobenius source gives the exact p^n logarithmic scaling. -/
theorem frobeniusLog_scaling (n : ℕ) (x : Tate D w) :
    frobeniusLog D w n x = (Arithmetic.residueChar w.1 ^ n) •
      InitialThetaDeRhamLogarithm.tateLog D w x := by
  rw [frobeniusLog_eq, tateLog_pow]

theorem phi_primitive :
    phi D w (InitialThetaTiltFontaine.primitive D w) =
      (WittVector.teichmuller (Arithmetic.residueChar w.1)
        (InitialThetaTiltFontaine.integralLift D w (Arithmetic.residueChar w.1))) ^
          Arithmetic.residueChar w.1 - Arithmetic.residueChar w.1 := by
  rw [InitialThetaTiltFontaine.primitive, map_sub, map_natCast, phi_teichmuller, ← map_pow]

theorem theta_phi_primitive :
    InitialThetaTiltFontaine.theta D w (phi D w (InitialThetaTiltFontaine.primitive D w)) =
      (Arithmetic.residueChar w.1 : LocalGeometricFontaine.integerRing (coefficientField D w)) ^
        Arithmetic.residueChar w.1 - Arithmetic.residueChar w.1 := by
  rw [phi_primitive, map_sub, map_pow, InitialThetaTiltFontaine.theta_integralLift, map_natCast]

theorem theta_phi_primitive_ne_zero :
    InitialThetaTiltFontaine.theta D w (phi D w (InitialThetaTiltFontaine.primitive D w)) ≠ 0 := by
  rw [theta_phi_primitive]
  apply sub_ne_zero.mpr
  intro h
  have hn : Arithmetic.residueChar w.1 < Arithmetic.residueChar w.1 ^ Arithmetic.residueChar w.1 :=
    Nat.lt_pow_self (Arithmetic.residueChar_prime w.1).one_lt
  have he : ((Arithmetic.residueChar w.1 ^ Arithmetic.residueChar w.1 : ℕ) :
      LocalGeometricFontaine.integerRing (coefficientField D w)) = Arithmetic.residueChar w.1 := by
    simpa only [Nat.cast_pow] using h
  exact hn.ne' (Nat.cast_injective he)

theorem phi_not_preserve_kernel :
    ∃ a ∈ RingHom.ker (InitialThetaTiltFontaine.theta D w),
      phi D w a ∉ RingHom.ker (InitialThetaTiltFontaine.theta D w) :=
  ⟨InitialThetaTiltFontaine.primitive D w, InitialThetaTiltFontaine.primitive_mem_kernel D w,
    theta_phi_primitive_ne_zero D w⟩

theorem phi_primitive_image_isUnit : IsUnit (InitialThetaDeRhamTeichmuller.ainfToPlus D w
    (phi D w (InitialThetaTiltFontaine.primitive D w))) := by
  apply (InitialThetaDeRhamCompletion.isUnit_iff D w _).mpr
  rw [InitialThetaDeRhamTeichmuller.theta_ainfToPlus]
  exact fun h => theta_phi_primitive_ne_zero D w (Subtype.ext h)

theorem phi_primitive_image_not_hasEval :
    ¬ PowerSeries.HasEval (InitialThetaDeRhamTeichmuller.ainfToPlus D w
      (phi D w (InitialThetaTiltFontaine.primitive D w))) := by
  obtain ⟨u, hu⟩ := phi_primitive_image_isUnit D w
  intro h
  have hn (n : ℕ) : ‖(InitialThetaDeRhamTeichmuller.ainfToPlus D w
      (phi D w (InitialThetaTiltFontaine.primitive D w))) ^ n‖ = 1 := by
    rw [← hu]
    simpa using InitialThetaDeRhamLogarithm.norm_unit D w (u ^ n)
  have ht0 : Filter.Tendsto (fun n : ℕ =>
      ‖(InitialThetaDeRhamTeichmuller.ainfToPlus D w
        (phi D w (InitialThetaTiltFontaine.primitive D w))) ^ n‖)
      Filter.atTop (𝓝 ‖(0 : InitialThetaDeRhamCompletion.Ring D w)‖) :=
    (continuous_norm.tendsto (0 : InitialThetaDeRhamCompletion.Ring D w)).comp h
  have ht : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 0) := by
    simpa only [hn, norm_zero] using ht0
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)

/-- This rules out precisely a continuous extension for the existing primitive-adic topology. -/
theorem no_continuous_frobenius_extension :
    ¬ ∃ F : InitialThetaDeRhamCompletion.Ring D w →+* InitialThetaDeRhamCompletion.Ring D w,
      Continuous F ∧ ∀ a : InitialThetaTiltFontaine.Ainf D w,
        F (InitialThetaDeRhamTeichmuller.ainfToPlus D w a) =
          InitialThetaDeRhamTeichmuller.ainfToPlus D w (phi D w a) := by
  rintro ⟨F, hF, hcomm⟩
  have hξ : PowerSeries.HasEval (InitialThetaDeRhamTeichmuller.ainfToPlus D w
      (InitialThetaTiltFontaine.primitive D w)) := by
    apply InitialThetaDeRhamLogarithm.hasEval_kernel D w
    rw [InitialThetaDeRhamTeichmuller.theta_ainfToPlus]
    exact congrArg (fun z : LocalGeometricFontaine.integerRing (coefficientField D w) =>
      (z : coefficientField D w)) (InitialThetaTiltFontaine.primitive_mem_kernel D w)
  apply phi_primitive_image_not_hasEval D w
  simpa only [hcomm] using hξ.map hF

end
end JoshiTeich.Act1Scene1.InitialThetaTateFrobenius
