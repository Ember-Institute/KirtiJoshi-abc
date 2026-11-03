import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoRealValue
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoCompletion
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoCompletion

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-WITT-RHO-COMPLETION-SOURCE
source: Joshi II `se:ff-rings`, rho norm completions and the original
actual/standard local-degree weighted value law.
fidelity: fixes the two normed source copies of the original bounded rings
at actual radius rho^localDeg and standard radius rho. The induced ring
equivalence saves the original functions and their proved ring laws; its norm-power law is
exactly the real value law already proved on the original rings.
Original proof; Scene1/Derived; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoCompletionComparison

open JoshiTeich.Prologue
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeCompletionSource : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Radius := PadicWittRhoCompletion.Radius

def actualRadius (ρ : Radius) : InitialThetaWittRhoCompletion.Radius :=
  ⟨ρ.val ^ Arithmetic.localDeg w.1,
    pos_iff_ne_zero.mpr (pow_ne_zero _ ρ.property.1.ne'),
    pow_lt_one₀ bot_le ρ.property.2 (Arithmetic.localDeg_pos w.1).ne'⟩

private def sourceFun (ρ : Radius)
    (x : InitialThetaWittRhoCompletion.Source D w (actualRadius D w ρ)) :
    PadicWittRhoCompletion.Source (Arithmetic.residueChar w.1) ρ :=
  (InitialThetaPadicBoundedWittComparison.ringEquiv D w).toEquiv.toFun x

private def sourceInvFun (_ρ : Radius) :=
  (InitialThetaPadicBoundedWittComparison.ringEquiv D w).toEquiv.invFun

set_option linter.defProp false in
private def source_left_inv (_ρ : Radius) :=
  (InitialThetaPadicBoundedWittComparison.ringEquiv D w).toEquiv.left_inv

set_option linter.defProp false in
private def source_right_inv (_ρ : Radius) :=
  (InitialThetaPadicBoundedWittComparison.ringEquiv D w).toEquiv.right_inv

set_option linter.defProp false in
private def source_map_add (_ρ : Radius) :=
  (InitialThetaPadicBoundedWittComparison.ringEquiv D w).map_add

set_option linter.defProp false in
private def source_map_mul (_ρ : Radius) :=
  (InitialThetaPadicBoundedWittComparison.ringEquiv D w).map_mul

def sourceRingEquiv (ρ : Radius) :
    InitialThetaWittRhoCompletion.Source D w (actualRadius D w ρ) ≃+*
      PadicWittRhoCompletion.Source (Arithmetic.residueChar w.1) ρ where
  toFun := sourceFun D w ρ
  invFun := sourceInvFun D w ρ
  left_inv := source_left_inv D w ρ
  right_inv := source_right_inv D w ρ
  map_add' := source_map_add D w ρ
  map_mul' := source_map_mul D w ρ

theorem source_norm_pow (ρ : Radius)
    (x : InitialThetaWittRhoCompletion.Source D w (actualRadius D w ρ)) :
    ‖sourceRingEquiv D w ρ x‖ ^ Arithmetic.localDeg w.1 = ‖x‖ := by
  change PadicWittRhoNorm.realValue (Arithmetic.residueChar w.1) ρ.val
      (InitialThetaPadicBoundedWittComparison.ringEquiv D w x) ^
      Arithmetic.localDeg w.1 =
    InitialThetaWittRhoNorm.realValue D w (ρ.val ^ Arithmetic.localDeg w.1) x
  exact InitialThetaPadicWittRhoComparison.realValue_pow D w ρ.val
    ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne x

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoCompletionComparison
