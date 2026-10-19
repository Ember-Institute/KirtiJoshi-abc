import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDeRhamTeichmuller

/-!
source-id: JT-SCENE1-INITIAL-THETA-TATE-DE-RHAM-PILOT
source: Joshi II pr:teichmuller-lift-A/B and thm:theta-pilot-object-appears
(940--1013), and the inclusion into B_dR (1069--1076).
fidelity: embeds the same D/w actual Tate parameter into its actual untilt,
constructs a 2-ell root there, and lifts its j^2 powers to the original
BDeRhamPlus through actual W(O_F). Proves the root equation, nonvanishing,
untilt-evaluation norm/log identities, product/sum laws and exact fibers.
This is one actual local untilt; it does not identify cross-holomorphoid
Ansatz points, paper theta-values, Frechet/rho norms or a Tate module.
Original proofs, no reference-engine copy; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot

open JoshiTeich.Prologue InitialThetaDeRhamCompletion
open InitialThetaCanonicalGeometricFontaine
open scoped BigOperators
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance primeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ < 1) := primeNormFact D w

def tateValue : coefficientField D w :=
  completionEmbedding D w ((iutInitialThetaTateParameterData D).parameter w.1)

theorem tateValue_ne_zero : tateValue D w ≠ 0 := by
  intro h
  exact (iutInitialThetaTateParameterData_laws D).parameter_nonzero w.1 w.2
    ((completionEmbedding D w).injective (h.trans (map_zero _).symm))

theorem tateValue_norm :
    ‖tateValue D w‖ = (iutInitialThetaTateParameterData D).norm w.1 := by
  rw [tateValue, completionEmbedding_norm]
  exact ((iutInitialThetaTateParameterData_laws D).norm_eq w.1 w.2).symm

theorem tateValue_norm_lt_one : ‖tateValue D w‖ < 1 := by
  rw [tateValue_norm]
  exact (iutInitialThetaTateParameterData_laws D).norm_lt_one w.1 w.2

theorem root_exists : ∃ x : coefficientField D w, x ^ (2 * D.prime.ℓ) = tateValue D w :=
  IsAlgClosed.exists_pow_nat_eq _ (Nat.mul_pos (by decide) D.prime.ℓ_prime.pos)

def root : coefficientField D w := (root_exists D w).choose

theorem root_pow : root D w ^ (2 * D.prime.ℓ) = tateValue D w := (root_exists D w).choose_spec

theorem root_ne_zero : root D w ≠ 0 := by
  intro h
  have hp : 2 * D.prime.ℓ ≠ 0 := Nat.mul_ne_zero (by decide) D.prime.ℓ_prime.ne_zero
  exact tateValue_ne_zero D w ((root_pow D w).symm.trans (by rw [h, zero_pow hp]))

theorem root_norm_pow : ‖root D w‖ ^ (2 * D.prime.ℓ) = ‖tateValue D w‖ := by
  rw [← norm_pow, root_pow]

theorem root_norm_lt_one : ‖root D w‖ < 1 := by
  have hp : 2 * D.prime.ℓ ≠ 0 := Nat.mul_ne_zero (by decide) D.prime.ℓ_prime.ne_zero
  apply (pow_lt_one_iff_of_nonneg (norm_nonneg _) hp).mp
  rw [root_norm_pow]
  exact tateValue_norm_lt_one D w

theorem root_log :
    Real.log ‖root D w‖ = Real.log ((iutInitialThetaTateParameterData D).norm w.1) /
      ((2 * D.prime.ℓ : ℕ) : ℝ) := by
  have hp : ((2 * D.prime.ℓ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by decide : (2 : ℕ) ≠ 0) D.prime.ℓ_prime.ne_zero
  apply (eq_div_iff hp).mpr
  have h := congrArg Real.log (root_norm_pow D w)
  rw [Real.log_pow, tateValue_norm] at h
  exact (mul_comm _ _).trans h

def integralRoot : LocalGeometricFontaine.integerRing (coefficientField D w) :=
  ⟨root D w, (LocalGeometricFontaine.mem_integerRing _ _).mpr (root_norm_lt_one D w).le⟩

def tiltRoot : InitialThetaTiltIntegers.Integers D w :=
  InitialThetaTiltFontaine.integralLift D w (integralRoot D w)

theorem tiltRoot_norm : ‖tiltRoot D w‖ = ‖root D w‖ :=
  InitialThetaTiltFontaine.integralLift_norm D w (integralRoot D w)

theorem tiltRoot_norm_lt_one : ‖tiltRoot D w‖ < 1 := by
  rw [tiltRoot_norm]
  exact root_norm_lt_one D w

def pilot (j : ℕ) : Ring D w :=
  InitialThetaDeRhamTeichmuller.lift D w (integralRoot D w) ^ (j ^ 2)

theorem pilot_isUnit (j : ℕ) : IsUnit (pilot D w j) :=
  (InitialThetaDeRhamTeichmuller.lift_isUnit D w (integralRoot D w)
    (fun h => root_ne_zero D w (congrArg Subtype.val h))).pow _

theorem theta_pilot (j : ℕ) : theta D w (pilot D w j) = root D w ^ (j ^ 2) :=
  InitialThetaDeRhamTeichmuller.theta_lift_pow D w (integralRoot D w) _

theorem theta_pilot_ne_zero (j : ℕ) : theta D w (pilot D w j) ≠ 0 := by
  rw [theta_pilot]
  exact pow_ne_zero _ (root_ne_zero D w)

theorem theta_pilot_root_equation (j : ℕ) :
    theta D w (pilot D w j) ^ (2 * D.prime.ℓ) = tateValue D w ^ (j ^ 2) := by
  rw [theta_pilot, ← pow_mul, Nat.mul_comm, pow_mul, root_pow]

theorem evaluation_norm (j : ℕ) : ‖theta D w (pilot D w j)‖ = ‖root D w‖ ^ (j ^ 2) := by
  rw [theta_pilot, norm_pow]

theorem evaluation_log (j : ℕ) :
    Real.log ‖theta D w (pilot D w j)‖ = (j ^ 2 : ℕ) * Real.log ‖root D w‖ := by
  rw [evaluation_norm, Real.log_pow]

theorem evaluation_log_eq_tate (j : ℕ) :
    Real.log ‖theta D w (pilot D w j)‖ =
      ((j ^ 2 : ℕ) : ℝ) / ((2 * D.prime.ℓ : ℕ) : ℝ) *
        Real.log ((iutInitialThetaTateParameterData D).norm w.1) := by
  rw [evaluation_log, root_log]
  ring

theorem evaluation_product {ι : Type*} (s : Finset ι) (j : ι → ℕ) :
    (∏ i ∈ s, ‖theta D w (pilot D w (j i))‖) = ‖root D w‖ ^ (∑ i ∈ s, j i ^ 2) := by
  simp_rw [evaluation_norm]
  exact (Finset.prod_pow_eq_pow_sum s (fun i => j i ^ 2) ‖root D w‖)

theorem evaluation_log_sum {ι : Type*} (s : Finset ι) (j : ι → ℕ) :
    (∑ i ∈ s, Real.log ‖theta D w (pilot D w (j i))‖) =
      (∑ i ∈ s, ((j i ^ 2 : ℕ) : ℝ)) * Real.log ‖root D w‖ := by
  simp_rw [evaluation_log]
  exact (Finset.sum_mul s (fun i => ((j i ^ 2 : ℕ) : ℝ)) _).symm

theorem fiber (j : ℕ) (a : Ring D w) :
    theta D w a = root D w ^ (j ^ 2) ↔
      ∃ b : Ring D w, a = primitive D w * b + pilot D w j := by
  constructor
  · intro ha
    have hk : a - pilot D w j ∈ RingHom.ker (theta D w) := by
      change theta D w (a - pilot D w j) = 0
      rw [map_sub, ha, theta_pilot, sub_self]
    rw [kernel_eq_span, Ideal.mem_span_singleton] at hk
    obtain ⟨b, hb⟩ := hk
    exact ⟨b, sub_eq_iff_eq_add.mp hb⟩
  · rintro ⟨b, rfl⟩
    rw [map_add, map_mul, theta_primitive, zero_mul, zero_add, theta_pilot]

end
end JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot
