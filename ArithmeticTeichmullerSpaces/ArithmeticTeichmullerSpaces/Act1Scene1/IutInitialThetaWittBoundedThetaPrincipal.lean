import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaQuotientTopology
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFontaineKernel

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-BOUNDED-THETA-PRINCIPAL
source: Joshi II `se:ff-rings`, `pr:primitive-elements1` and
`pr:teichmuller-lift-A`, the actual primitive Fontaine kernel.
fidelity: localizes the proved original Ainf kernel identity through
the actual bounded denominator. Constructs original bounded-source
Teichmuller corrections lifting every small untilt value, agreeing
with the existing common-ring local lift that tends to zero.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no principal kernel in the completed ring or
full Frobenius-eigen kernel identity is assumed. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittBoundedThetaPrincipal

open JoshiTeich.Prologue InitialThetaWittThetaBound
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def boundedPrimitive : InitialThetaBoundedWittLocalization.Ring D w :=
  InitialThetaBoundedWittLocalization.inclusion D w (InitialThetaTiltFontaine.primitive D w)

theorem boundedPrimitive_evaluation : InitialThetaBoundedWittLocalization.evaluation D w
    (boundedPrimitive D w) = 0 := by
  rw [boundedPrimitive, InitialThetaBoundedWittLocalization.evaluation_inclusion]
  exact congrArg Subtype.val (InitialThetaTiltFontaine.primitive_mem_kernel D w)

theorem bounded_evaluation_eq_zero_iff_dvd (x : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaBoundedWittLocalization.evaluation D w x = 0 ↔ boundedPrimitive D w ∣ x := by
  constructor
  · intro hx
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (InitialThetaBoundedWittLocalization.denominator D w) x
    have he := congrArg (InitialThetaBoundedWittLocalization.evaluation D w) ha
    rw [map_mul, hx, zero_mul] at he
    change 0 = InitialThetaBoundedWittLocalization.evaluation D w
      (InitialThetaBoundedWittLocalization.inclusion D w a) at he
    rw [InitialThetaBoundedWittLocalization.evaluation_inclusion] at he
    have hz : InitialThetaTiltFontaine.theta D w a = 0 := Subtype.ext he.symm
    obtain ⟨b, hb⟩ := (InitialThetaFontaineKernel.mem_kernel_iff_dvd D w a).mp hz
    obtain ⟨v, hv⟩ := (IsLocalization.Away.algebraMap_isUnit (InitialThetaBoundedWittLocalization.denominator D w)
      (S := InitialThetaBoundedWittLocalization.Ring D w)).pow n
    have hm : x * v.val = boundedPrimitive D w * InitialThetaBoundedWittLocalization.inclusion D w b := by
      rw [hv, ha, hb, map_mul]
      rfl
    refine ⟨InitialThetaBoundedWittLocalization.inclusion D w b * (v⁻¹).val, ?_⟩
    calc
      x = (x * v.val) * (v⁻¹).val := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [hm, mul_assoc]
  · rintro ⟨b, rfl⟩
    rw [map_mul, boundedPrimitive_evaluation, zero_mul]

theorem bounded_kernel_eq_span : RingHom.ker (InitialThetaBoundedWittLocalization.evaluation D w) =
    Ideal.span {boundedPrimitive D w} := by
  ext x
  exact (bounded_evaluation_eq_zero_iff_dvd D w x).trans Ideal.mem_span_singleton.symm

def localSourceLift (z : Untilt D w) : InitialThetaBoundedWittLocalization.Ring D w :=
  if hz : ‖z‖ ≤ 1 then
    InitialThetaBoundedWittLocalization.inclusion D w
      (WittVector.teichmuller (Arithmetic.residueChar w.1)
        (InitialThetaTiltFontaine.integralLift D w ⟨z, (LocalGeometricFontaine.mem_integerRing _ _).mpr hz⟩))
  else 0

theorem inclusion_localSourceLift (z : Untilt D w) :
    InitialThetaWittAllRadiusCompletion.inclusion D w (localSourceLift D w z) =
      InitialThetaWittThetaQuotientTopology.localLift D w z := by
  unfold localSourceLift InitialThetaWittThetaQuotientTopology.localLift
  split_ifs with hz
  · rfl
  · exact map_zero _

theorem evaluation_localSourceLift (z : Untilt D w) (hz : ‖z‖ ≤ 1) :
    InitialThetaBoundedWittLocalization.evaluation D w (localSourceLift D w z) = z := by
  rw [← InitialThetaWittThetaEvaluation.evaluation_inclusion, inclusion_localSourceLift]
  exact InitialThetaWittThetaQuotientTopology.evaluation_localLift D w z hz

def corrected (x : InitialThetaBoundedWittLocalization.Ring D w) : InitialThetaBoundedWittLocalization.Ring D w :=
  x - localSourceLift D w (InitialThetaBoundedWittLocalization.evaluation D w x)

theorem corrected_evaluation (x : InitialThetaBoundedWittLocalization.Ring D w)
    (hx : ‖InitialThetaBoundedWittLocalization.evaluation D w x‖ ≤ 1) :
    InitialThetaBoundedWittLocalization.evaluation D w (corrected D w x) = 0 := by
  rw [corrected, map_sub, evaluation_localSourceLift D w _ hx, sub_self]

theorem inclusion_corrected (x : InitialThetaBoundedWittLocalization.Ring D w) :
    InitialThetaWittAllRadiusCompletion.inclusion D w (corrected D w x) =
      InitialThetaWittAllRadiusCompletion.inclusion D w x -
        InitialThetaWittThetaQuotientTopology.localLift D w
          (InitialThetaWittThetaEvaluation.evaluation D w (InitialThetaWittAllRadiusCompletion.inclusion D w x)) := by
  rw [corrected, map_sub, inclusion_localSourceLift, InitialThetaWittThetaEvaluation.evaluation_inclusion]

end
end JoshiTeich.Act1Scene1.InitialThetaWittBoundedThetaPrincipal
