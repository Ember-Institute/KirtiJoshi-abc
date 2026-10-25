import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittProductFrobenius

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ALL-RADIUS-FROBENIUS
source: Joshi II `se:ff-rings`, invertible continuous Frobenius on the
period ring equipped with its family of rho norms.
fidelity: proves that the product Frobenius and its inverse preserve
the closure of the original bounded localization diagonal. Restricts
them to a continuous ring automorphism of the existing common complete
ring, with exact inclusion, coordinate and seminorm identities.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; scalar algebra, multiplicative norm equality,
Tate-log eigenspace and paper B/BK identities remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittAllRadiusFrobenius

open JoshiTeich.Prologue
open InitialThetaWittAllRadiusCompletion InitialThetaWittProductFrobenius
open InitialThetaWittRhoFrobeniusCompletion InitialThetaWittRhoFrobeniusEquiv
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

theorem productEquiv_mem_common (x : InitialThetaWittAllRadiusCompletion.Product D w)
    (hx : x ∈ commonSubring D w) : productEquiv D w x ∈ commonSubring D w := by
  change x ∈ closure (Set.range (diagonal D w)) at hx
  change productEquiv D w x ∈ closure (Set.range (diagonal D w))
  apply closure_mono ?_ (mem_closure_image (productEquiv_continuous D w).continuousAt hx)
  rintro y ⟨z, ⟨a, rfl⟩, rfl⟩
  exact ⟨InitialThetaBoundedWittLocalization.frobeniusEquiv D w a,
    (productEquiv_diagonal D w a).symm⟩

theorem productEquiv_symm_mem_common (x : InitialThetaWittAllRadiusCompletion.Product D w)
    (hx : x ∈ commonSubring D w) : (productEquiv D w).symm x ∈ commonSubring D w := by
  change x ∈ closure (Set.range (diagonal D w)) at hx
  change (productEquiv D w).symm x ∈ closure (Set.range (diagonal D w))
  apply closure_mono ?_ (mem_closure_image (productEquiv_symm_continuous D w).continuousAt hx)
  rintro y ⟨z, ⟨a, rfl⟩, rfl⟩
  exact ⟨(InitialThetaBoundedWittLocalization.frobeniusEquiv D w).symm a,
    (productEquiv_symm_diagonal D w a).symm⟩

def frobeniusHom : Carrier D w →+* Carrier D w :=
  ((productEquiv D w).toRingHom.comp (commonSubring D w).subtype).codRestrict
    (commonSubring D w) (fun x => productEquiv_mem_common D w x.val x.property)

def inverseHom : Carrier D w →+* Carrier D w :=
  ((productEquiv D w).symm.toRingHom.comp (commonSubring D w).subtype).codRestrict
    (commonSubring D w) (fun x => productEquiv_symm_mem_common D w x.val x.property)

def frobeniusEquiv : Carrier D w ≃+* Carrier D w where
  __ := frobeniusHom D w
  invFun := inverseHom D w
  left_inv x := Subtype.ext ((productEquiv D w).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((productEquiv D w).apply_symm_apply x.val)

theorem frobenius_continuous : Continuous (frobeniusEquiv D w) :=
  ((productEquiv_continuous D w).comp continuous_subtype_val).subtype_mk _

theorem inverse_continuous : Continuous (frobeniusEquiv D w).symm :=
  ((productEquiv_symm_continuous D w).comp continuous_subtype_val).subtype_mk _

theorem frobenius_inclusion (x : InitialThetaBoundedWittLocalization.Ring D w) :
    frobeniusEquiv D w (inclusion D w x) =
      inclusion D w (InitialThetaBoundedWittLocalization.frobeniusEquiv D w x) :=
  Subtype.ext (productEquiv_diagonal D w x)

theorem inverse_inclusion (x : InitialThetaBoundedWittLocalization.Ring D w) :
    (frobeniusEquiv D w).symm (inclusion D w x) =
      inclusion D w ((InitialThetaBoundedWittLocalization.frobeniusEquiv D w).symm x) :=
  Subtype.ext (productEquiv_symm_diagonal D w x)

theorem evaluate_frobenius (ρ : Radius) (x : Carrier D w) :
    evaluate D w (poweredRadius D w ρ) (frobeniusEquiv D w x) =
      completedEquiv D w ρ (evaluate D w ρ x) :=
  productEquiv_powered D w x.val ρ

theorem evaluate_inverse (ρ : Radius) (x : Carrier D w) :
    evaluate D w ρ ((frobeniusEquiv D w).symm x) =
      (completedEquiv D w ρ).symm (evaluate D w (poweredRadius D w ρ) x) := rfl

theorem coordinateSeminorm_frobenius (ρ : Radius) (x : Carrier D w) :
    coordinateSeminorm D w (poweredRadius D w ρ) (frobeniusEquiv D w x) =
      coordinateSeminorm D w ρ x ^ Arithmetic.residueChar w.1 := by
  change ‖evaluate D w (poweredRadius D w ρ) (frobeniusEquiv D w x)‖ =
    ‖evaluate D w ρ x‖ ^ Arithmetic.residueChar w.1
  rw [evaluate_frobenius, completedEquiv_apply, completedHom_norm]

theorem coordinateSeminorm_inverse (ρ : Radius) (x : Carrier D w) :
    coordinateSeminorm D w ρ ((frobeniusEquiv D w).symm x) ^ Arithmetic.residueChar w.1 =
      coordinateSeminorm D w (poweredRadius D w ρ) x := by
  change ‖evaluate D w ρ ((frobeniusEquiv D w).symm x)‖ ^ Arithmetic.residueChar w.1 =
    ‖evaluate D w (poweredRadius D w ρ) x‖
  rw [evaluate_inverse, completedEquiv_symm_norm]

def frobeniusHomeomorph : Carrier D w ≃ₜ Carrier D w where
  toEquiv := (frobeniusEquiv D w).toEquiv
  continuous_toFun := frobenius_continuous D w
  continuous_invFun := inverse_continuous D w

end
end JoshiTeich.Act1Scene1.InitialThetaWittAllRadiusFrobenius
