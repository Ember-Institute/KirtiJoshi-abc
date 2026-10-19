import ArithmeticTeichmullerSpaces.Act1Scene1.FiniteCompletionEmbedding
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTateDeRhamPilot
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaQRootFamilyLocalLaws

/-!
source-id: JT-SCENE1-INITIAL-THETA-TORSION-DE-RHAM-PILOT
source: Joshi II pr:teichmuller-lift-A/B and the local pilot (940--1013);
Joshi III local relative-degree weights; actual torsion q-root power laws.
fidelity: embeds the original torsion completion into the same actual untilt
over its original base completion, and lifts the original q-root image into
the same BDeRhamPlus. Proves exact equations, relative-degree norm accounting
and comparison with the previous local pilot by an actual root of unity.
No raw norm isometry, cross-holomorphoid identity, Frechet norm or paper
theta-locus identity is asserted. Original proofs; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot

open JoshiTeich.Prologue InitialThetaDeRhamCompletion InitialThetaCanonicalGeometricFontaine
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
variable (v : NumberField.FinitePlace ↥D.prime.torsionField)
variable (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.1.maximalIdeal.asIdeal)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance primeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ < 1) := primeNormFact D w

def embedding : LocalCompletion.completionAt ↥D.prime.torsionField v →+* coefficientField D w :=
  FiniteCompletionEmbedding.embedding hvw (completionEmbedding D w)

theorem embedding_base (x : LocalCompletion.completionAt D.F w.1) :
    embedding D w v hvw (iutEmbedCompletion hvw x) = completionEmbedding D w x :=
  FiniteCompletionEmbedding.embedding_base hvw (completionEmbedding D w) x

theorem embedding_injective : Function.Injective (embedding D w v hvw) :=
  FiniteCompletionEmbedding.embedding_injective hvw (completionEmbedding D w)

theorem supported_bad : w.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
  (Set.ext_iff.mp (iutInitialThetaTateParameterData_places_eq D) w.1).mpr w.2

theorem parameter_eq_tate : (iutInitialThetaTateParameterData D).parameter w.1 =
    (D.prime.tate w.1 (supported_bad D w)).q := by
  classical
  change (if hw : w.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad then
    ((D.prime.tate w.1 hw).q : LocalCompletion.completionAt D.F w.1) else 0) = _
  rw [dite_eq_left (supported_bad D w)]

theorem qroot_power : IutInitialThetaQRootFamily.qrootAt D v ^ (2 * D.prime.ℓ) =
    iutEmbedCompletion hvw ((iutInitialThetaTateParameterData D).parameter w.1) := by
  rw [parameter_eq_tate]
  exact IutInitialThetaQRootFamily.qrootAt_pow_eq_of_liesOver D hvw (supported_bad D w)

def rootImage : coefficientField D w := embedding D w v hvw (IutInitialThetaQRootFamily.qrootAt D v)

theorem rootImage_pow : rootImage D w v hvw ^ (2 * D.prime.ℓ) =
    InitialThetaTateDeRhamPilot.tateValue D w := by
  rw [rootImage, ← map_pow, qroot_power D w v hvw, embedding_base D w v hvw]
  rfl

theorem rootImage_ne_zero : rootImage D w v hvw ≠ 0 := by
  intro h
  exact IutInitialThetaQRootFamily.qrootAt_ne_zero D v
    (embedding_injective D w v hvw (h.trans (map_zero _).symm))

theorem rootImage_norm_pow : ‖rootImage D w v hvw‖ ^ (2 * D.prime.ℓ) =
    ‖(iutInitialThetaTateParameterData D).parameter w.1‖ := by
  rw [← norm_pow, rootImage_pow, InitialThetaTateDeRhamPilot.tateValue, completionEmbedding_norm]

theorem rootImage_norm : ‖rootImage D w v hvw‖ = ‖InitialThetaTateDeRhamPilot.root D w‖ := by
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _)
    (Nat.mul_ne_zero (by decide : (2 : ℕ) ≠ 0) D.prime.ℓ_prime.ne_zero)).mp
  rw [← norm_pow, rootImage_pow, ← norm_pow, InitialThetaTateDeRhamPilot.root_pow]

theorem rootImage_norm_lt_one : ‖rootImage D w v hvw‖ < 1 := by
  rw [rootImage_norm]
  exact InitialThetaTateDeRhamPilot.root_norm_lt_one D w

theorem qroot_norm_eq_image_pow : ‖IutInitialThetaQRootFamily.qrootAt D v‖ =
    ‖rootImage D w v hvw‖ ^
      (iutRelativeRamificationIndex (v := v) (w := w.1) * Arithmetic.relInertDeg v w.1) := by
  have hn : 2 * D.prime.ℓ ≠ 0 := Nat.mul_ne_zero (by decide) D.prime.ℓ_prime.ne_zero
  apply (pow_left_inj₀ (norm_nonneg _) (pow_nonneg (norm_nonneg _) _) hn).mp
  have hraw := congrArg norm (qroot_power D w v hvw)
  rw [norm_pow, iutEmbedCompletion_norm_eq_pow] at hraw
  calc
    _ = _ := hraw
    _ = (‖rootImage D w v hvw‖ ^ (2 * D.prime.ℓ)) ^
        (iutRelativeRamificationIndex (v := v) (w := w.1) * Arithmetic.relInertDeg v w.1) := by
      rw [rootImage_norm_pow]
    _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem qroot_log_eq_degree_mul : Real.log ‖IutInitialThetaQRootFamily.qrootAt D v‖ =
    ((iutRelativeRamificationIndex (v := v) (w := w.1) * Arithmetic.relInertDeg v w.1 : ℕ) : ℝ) *
      Real.log ‖rootImage D w v hvw‖ := by
  rw [qroot_norm_eq_image_pow, Real.log_pow]

def phase : coefficientField D w := rootImage D w v hvw / InitialThetaTateDeRhamPilot.root D w

theorem phase_pow : phase D w v hvw ^ (2 * D.prime.ℓ) = 1 := by
  rw [phase, div_pow, rootImage_pow, InitialThetaTateDeRhamPilot.root_pow]
  exact div_self (InitialThetaTateDeRhamPilot.tateValue_ne_zero D w)

theorem phase_norm : ‖phase D w v hvw‖ = 1 := by
  rw [phase, norm_div, rootImage_norm]
  exact div_self (norm_ne_zero_iff.mpr (InitialThetaTateDeRhamPilot.root_ne_zero D w))

def integralImage : LocalGeometricFontaine.integerRing (coefficientField D w) :=
  ⟨rootImage D w v hvw, (LocalGeometricFontaine.mem_integerRing _ _).mpr
    (rootImage_norm_lt_one D w v hvw).le⟩

def pilot (j : ℕ) : Ring D w :=
  InitialThetaDeRhamTeichmuller.lift D w (integralImage D w v hvw) ^ (j ^ 2)

theorem theta_pilot (j : ℕ) : theta D w (pilot D w v hvw j) = rootImage D w v hvw ^ (j ^ 2) :=
  InitialThetaDeRhamTeichmuller.theta_lift_pow D w (integralImage D w v hvw) _

theorem theta_pilot_eq_phase_mul (j : ℕ) : theta D w (pilot D w v hvw j) =
    phase D w v hvw ^ (j ^ 2) * theta D w (InitialThetaTateDeRhamPilot.pilot D w j) := by
  rw [theta_pilot, InitialThetaTateDeRhamPilot.theta_pilot, ← mul_pow]
  congr 1
  exact (div_mul_cancel₀ _ (InitialThetaTateDeRhamPilot.root_ne_zero D w)).symm

theorem evaluation_norm (j : ℕ) :
    ‖theta D w (pilot D w v hvw j)‖ = ‖theta D w (InitialThetaTateDeRhamPilot.pilot D w j)‖ := by
  rw [theta_pilot, InitialThetaTateDeRhamPilot.theta_pilot, norm_pow, norm_pow, rootImage_norm]

theorem evaluation_log_eq_tate (j : ℕ) :
    Real.log ‖theta D w (pilot D w v hvw j)‖ =
      ((j ^ 2 : ℕ) : ℝ) / ((2 * D.prime.ℓ : ℕ) : ℝ) *
        Real.log ((iutInitialThetaTateParameterData D).norm w.1) := by
  rw [evaluation_norm, InitialThetaTateDeRhamPilot.evaluation_log_eq_tate]

end
end JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot
