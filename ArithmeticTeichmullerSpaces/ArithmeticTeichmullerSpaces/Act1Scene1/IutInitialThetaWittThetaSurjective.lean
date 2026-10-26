import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaTateFiber

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-THETA-SURJECTIVE
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, the
canonical period-ring evaluation onto the original untilt.
fidelity: scales every untilt element into its original valuation ring
by an actual power of p, lifts it through the original integral
Teichmuller lift and inverts that same power in the bounded Witt ring.
Thus both the original bounded evaluation and its completed evaluations
are surjective. The common ring has a closed maximal evaluation kernel
and the algebraic quotient is the original untilt.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; openness and the quotient topology are
separate consumers. No principal-kernel or arbitrary-untilt assertion.
Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittThetaSurjective

open JoshiTeich.Prologue InitialThetaWittThetaBound InitialThetaWittThetaEvaluation
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem exists_integral_prime_scale (z : Untilt D w) :
    ∃ m : ℕ, ‖(Arithmetic.residueChar w.1 : Untilt D w) ^ m * z‖ ≤ 1 := by
  by_cases hz : z = 0
  · exact ⟨0, by rw [hz, mul_zero, norm_zero]; exact zero_le_one⟩
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hz0)
    (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out.2
  refine ⟨m, ?_⟩
  rw [norm_mul, norm_pow]
  exact ((lt_div_iff₀ hz0).mp hm).le

theorem boundedEvaluation_surjective :
    Function.Surjective (InitialThetaBoundedWittLocalization.evaluation D w) := by
  intro z
  obtain ⟨m, hm⟩ := exists_integral_prime_scale D w z
  let zO : LocalGeometricFontaine.integerRing (Untilt D w) :=
    ⟨(Arithmetic.residueChar w.1 : Untilt D w) ^ m * z,
      (LocalGeometricFontaine.mem_integerRing _ _).mpr hm⟩
  let a : Ainf D w := WittVector.teichmuller (Arithmetic.residueChar w.1)
    (InitialThetaTiltFontaine.integralLift D w zO)
  obtain ⟨v, hv⟩ := (InitialThetaBoundedWittLocalization.prime_isUnit D w).pow m
  let x : InitialThetaBoundedWittLocalization.Ring D w :=
    InitialThetaBoundedWittLocalization.inclusion D w a * (v⁻¹ : _)
  have hx : x * InitialThetaBoundedWittLocalization.inclusion D w (Arithmetic.residueChar w.1) ^ m =
      InitialThetaBoundedWittLocalization.inclusion D w a := by
    dsimp only [x]
    rw [← hv, mul_assoc, Units.inv_mul, mul_one]
  have ha : InitialThetaBoundedWittLocalization.evaluation D w
      (InitialThetaBoundedWittLocalization.inclusion D w a) =
      (Arithmetic.residueChar w.1 : Untilt D w) ^ m * z :=
    (InitialThetaBoundedWittLocalization.evaluation_inclusion D w a).trans
      (congrArg Subtype.val (InitialThetaTiltFontaine.theta_integralLift D w zO))
  have he : InitialThetaBoundedWittLocalization.evaluation D w x *
      (Arithmetic.residueChar w.1 : Untilt D w) ^ m =
      z * (Arithmetic.residueChar w.1 : Untilt D w) ^ m := by
    have h := congrArg (InitialThetaBoundedWittLocalization.evaluation D w) hx
    simpa only [map_mul, map_pow, map_natCast, ha, mul_comm] using h
  exact ⟨x, mul_right_cancel₀ (pow_ne_zero m
    (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)) he⟩

theorem evaluation_surjective : Function.Surjective (evaluation D w) := by
  intro z
  obtain ⟨x, hx⟩ := boundedEvaluation_surjective D w z
  exact ⟨InitialThetaWittAllRadiusCompletion.inclusion D w x, (evaluation_inclusion D w x).trans hx⟩

theorem completedHom_surjective : Function.Surjective (completedHom D w) := by
  intro z
  obtain ⟨x, hx⟩ := boundedEvaluation_surjective D w z
  exact ⟨InitialThetaWittRhoCompletion.inclusion D w (radius D w) x,
    (completedHom_inclusion D w x).trans hx⟩

theorem kernel_isMaximal : (RingHom.ker (evaluation D w)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (evaluation D w) (evaluation_surjective D w)

theorem kernel_isClosed : IsClosed (RingHom.ker (evaluation D w) :
    Set (InitialThetaWittAllRadiusCompletion.Carrier D w)) :=
  isClosed_singleton.preimage (evaluation_continuous D w)

def quotientEquiv :
    (InitialThetaWittAllRadiusCompletion.Carrier D w ⧸ RingHom.ker (evaluation D w)) ≃+* Untilt D w :=
  (evaluation D w).quotientKerEquivOfSurjective (evaluation_surjective D w)

theorem quotientEquiv_mk (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    quotientEquiv D w (Ideal.Quotient.mk (RingHom.ker (evaluation D w)) x) = evaluation D w x :=
  RingHom.quotientKerEquivOfSurjective_apply_mk _ _

end
end JoshiTeich.Act1Scene1.InitialThetaWittThetaSurjective
