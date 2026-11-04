import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoProductDiagonal
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAllRadiusNativeDiagonal
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicBoundedWittMapLaws

/-!
source-id: JT-SCENE1-ACTUAL-STANDARD-PADIC-WITT-ALL-RADIUS-COMPARISON
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the family of
rho norms and completion of the original bounded Witt period subring.
fidelity: restricts the existing product equivalence to the closures of the
original bounded-ring diagonals. The standard closure is rewritten using
its p-only native diagonal identity, without changing either commonSubring
or Carrier. Both restricted maps are continuous and preserve the proved
local-degree coordinate norm power law. The original actual inclusion maps
to the native presentation of the original standard diagonal under ringFun,
which is separately proved equal to the original bounded ring map.
Original proof; Scene1/Derived; Prologue R5 unchanged.
boundary: pointwise wrappers using the old standard named inclusion,
paper B marking, scalar/Galois/period transport, general E variants and
H1e/BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittAllRadiusComparison

open JoshiTeich.Prologue
open InitialThetaPadicWittRhoCompletionComparison
open InitialThetaPadicWittRhoProductEquiv
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

-- Forward closure membership: actual → standard.
theorem productEquiv_symm_mem_common
    (x : InitialThetaWittAllRadiusCompletion.Product D w)
    (hx : x ∈ InitialThetaWittAllRadiusCompletion.commonSubring D w) :
    (productEquiv D w).symm x ∈
      PadicWittAllRadiusCompletion.commonSubring (Arithmetic.residueChar w.1) := by
  change x ∈ closure (Set.range (InitialThetaWittAllRadiusCompletion.diagonal D w)) at hx
  apply (PadicWittAllRadiusCompletion.mem_common_iff_mem_closure_diagonalFun
    (Arithmetic.residueChar w.1) ((productEquiv D w).symm x)).mpr
  apply closure_mono ?_
    (mem_closure_image (productEquiv_symm_continuous D w).continuousAt hx)
  rintro y ⟨z, ⟨a, rfl⟩, rfl⟩
  exact ⟨InitialThetaPadicBoundedWittComparison.ringFun D w a,
    (productEquiv_symm_diagonalFun D w a).symm⟩

-- The original saved bounded map supplies every standard source witness.
theorem productEquiv_mem_common
    (x : PadicWittAllRadiusCompletion.Product (Arithmetic.residueChar w.1))
    (hx : x ∈ PadicWittAllRadiusCompletion.commonSubring (Arithmetic.residueChar w.1)) :
    productEquiv D w x ∈ InitialThetaWittAllRadiusCompletion.commonSubring D w := by
  have hx' := (PadicWittAllRadiusCompletion.mem_common_iff_mem_closure_diagonalFun
    (Arithmetic.residueChar w.1) x).mp hx
  change productEquiv D w x ∈ closure
    (Set.range (InitialThetaWittAllRadiusCompletion.diagonal D w))
  apply closure_mono ?_
    (mem_closure_image (productEquiv_continuous D w).continuousAt hx')
  rintro y ⟨z, ⟨b, rfl⟩, rfl⟩
  obtain ⟨a, rfl⟩ := InitialThetaPadicBoundedWittComparison.ringFun_surjective D w b
  exact ⟨a, (productEquiv_diagonalFun D w a).symm⟩

-- Both homs are restrictions of the existing product maps.
def toStandard : InitialThetaWittAllRadiusCompletion.Carrier D w →+*
    PadicWittAllRadiusCompletion.Carrier (Arithmetic.residueChar w.1) :=
  ((productEquiv D w).symm.toRingHom.comp
      (InitialThetaWittAllRadiusCompletion.commonSubring D w).subtype).codRestrict
    (PadicWittAllRadiusCompletion.commonSubring (Arithmetic.residueChar w.1))
    (fun x => productEquiv_symm_mem_common D w x.val x.property)

def toActual : PadicWittAllRadiusCompletion.Carrier (Arithmetic.residueChar w.1) →+*
    InitialThetaWittAllRadiusCompletion.Carrier D w :=
  ((productEquiv D w).toRingHom.comp
      (PadicWittAllRadiusCompletion.commonSubring (Arithmetic.residueChar w.1)).subtype).codRestrict
    (InitialThetaWittAllRadiusCompletion.commonSubring D w)
    (fun x => productEquiv_mem_common D w x.val x.property)

def ringEquiv : InitialThetaWittAllRadiusCompletion.Carrier D w ≃+*
    PadicWittAllRadiusCompletion.Carrier (Arithmetic.residueChar w.1) where
  __ := toStandard D w
  invFun := toActual D w
  left_inv x := Subtype.ext ((productEquiv D w).apply_symm_apply x.val)
  right_inv x := Subtype.ext ((productEquiv D w).symm_apply_apply x.val)

theorem ringEquiv_continuous : Continuous (ringEquiv D w) :=
  ((productEquiv_symm_continuous D w).comp continuous_subtype_val).subtype_mk _

theorem ringEquiv_symm_continuous : Continuous (ringEquiv D w).symm :=
  ((productEquiv_continuous D w).comp continuous_subtype_val).subtype_mk _

theorem ringEquiv_inclusion_val (x : InitialThetaBoundedWittLocalization.Ring D w) :
    (ringEquiv D w (InitialThetaWittAllRadiusCompletion.inclusion D w x)).val =
      PadicWittAllRadiusCompletion.diagonalFun (Arithmetic.residueChar w.1)
        (InitialThetaPadicBoundedWittComparison.ringFun D w x) :=
  productEquiv_symm_diagonalFun D w x

theorem evaluate_ringEquiv (ρ : PadicWittRhoCompletion.Radius)
    (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    PadicWittAllRadiusCompletion.evaluate (Arithmetic.residueChar w.1) ρ
        (ringEquiv D w x) =
      completedRingEquiv D w ρ
        (InitialThetaWittAllRadiusCompletion.evaluate D w (actualRadius D w ρ) x) :=
  productEquiv_symm_apply D w x.val ρ

theorem evaluate_ringEquiv_symm (ρ : PadicWittRhoCompletion.Radius)
    (x : PadicWittAllRadiusCompletion.Carrier (Arithmetic.residueChar w.1)) :
    InitialThetaWittAllRadiusCompletion.evaluate D w (actualRadius D w ρ)
        ((ringEquiv D w).symm x) =
      (completedRingEquiv D w ρ).symm
        (PadicWittAllRadiusCompletion.evaluate (Arithmetic.residueChar w.1) ρ x) :=
  productEquiv_actual D w x.val ρ

theorem coordinateSeminorm_ringEquiv_pow (ρ : PadicWittRhoCompletion.Radius)
    (x : InitialThetaWittAllRadiusCompletion.Carrier D w) :
    PadicWittAllRadiusCompletion.coordinateSeminorm (Arithmetic.residueChar w.1) ρ
        (ringEquiv D w x) ^ Arithmetic.localDeg w.1 =
      InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w
        (actualRadius D w ρ) x := by
  change ‖PadicWittAllRadiusCompletion.evaluate (Arithmetic.residueChar w.1) ρ
      (ringEquiv D w x)‖ ^ Arithmetic.localDeg w.1 =
    ‖InitialThetaWittAllRadiusCompletion.evaluate D w (actualRadius D w ρ) x‖
  rw [evaluate_ringEquiv]
  exact completedRingEquiv_norm_pow D w ρ _

theorem coordinateSeminorm_ringEquiv_symm (ρ : PadicWittRhoCompletion.Radius)
    (x : PadicWittAllRadiusCompletion.Carrier (Arithmetic.residueChar w.1)) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w (actualRadius D w ρ)
        ((ringEquiv D w).symm x) =
      PadicWittAllRadiusCompletion.coordinateSeminorm (Arithmetic.residueChar w.1) ρ x ^
        Arithmetic.localDeg w.1 := by
  have h := coordinateSeminorm_ringEquiv_pow D w ρ ((ringEquiv D w).symm x)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

def homeomorph : InitialThetaWittAllRadiusCompletion.Carrier D w ≃ₜ
    PadicWittAllRadiusCompletion.Carrier (Arithmetic.residueChar w.1) where
  toEquiv := (ringEquiv D w).toEquiv
  continuous_toFun := ringEquiv_continuous D w
  continuous_invFun := ringEquiv_symm_continuous D w

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittAllRadiusComparison
