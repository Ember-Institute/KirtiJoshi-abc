import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittProductFrobenius

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-ALL-RADIUS-FROBENIUS
source: Joshi II `se:ff-rings`, invertible continuous Frobenius on the
standard period ring equipped with its family of rho norms.
fidelity: restricts the product Frobenius and its inverse to the closure
of the original bounded localization diagonal. It constructs a continuous
ring automorphism of the existing common complete ring and proves exact
inclusion, evaluation and coordinate seminorm identities.
boundary: Scene1/Derived; scalar algebra, Tate-log eigenspace and paper
B/BK identities remain open.
-/

namespace JoshiTeich.Act1Scene1.PadicWittAllRadiusFrobenius

open PadicBoundedWittLocalization
open PadicWittAllRadiusCompletion PadicWittProductFrobenius
open PadicWittRhoFrobeniusCompletion
open scoped ENNReal Topology
noncomputable section

variable (p : ℕ) [Fact p.Prime]

theorem productEquiv_mem_common (x : PadicWittAllRadiusCompletion.Product p)
    (hx : x ∈ commonSubring p) : productEquiv p x ∈ commonSubring p := by
  change x ∈ closure (Set.range (diagonal p)) at hx
  change productEquiv p x ∈ closure (Set.range (diagonal p))
  apply closure_mono ?_ (mem_closure_image (productEquiv_continuous p).continuousAt hx)
  rintro y ⟨z, ⟨a, rfl⟩, rfl⟩
  exact ⟨PadicWittRhoFrobenius.frobeniusEquiv p a,
    (productEquiv_diagonal p a).symm⟩

theorem productEquiv_symm_mem_common (x : PadicWittAllRadiusCompletion.Product p)
    (hx : x ∈ commonSubring p) : (productEquiv p).symm x ∈ commonSubring p := by
  change x ∈ closure (Set.range (diagonal p)) at hx
  change (productEquiv p).symm x ∈ closure (Set.range (diagonal p))
  apply closure_mono ?_ (mem_closure_image (productEquiv_symm_continuous p).continuousAt hx)
  rintro y ⟨z, ⟨a, rfl⟩, rfl⟩
  exact ⟨(PadicWittRhoFrobenius.frobeniusEquiv p).symm a,
    (productEquiv_symm_diagonal p a).symm⟩

def frobeniusHom : Carrier p →+* Carrier p :=
  ((productEquiv p).toRingHom.comp (commonSubring p).subtype).codRestrict
    (commonSubring p) (fun x => productEquiv_mem_common p x.val x.property)

def inverseHom : Carrier p →+* Carrier p :=
  ((productEquiv p).symm.toRingHom.comp (commonSubring p).subtype).codRestrict
    (commonSubring p) (fun x => productEquiv_symm_mem_common p x.val x.property)

def frobeniusEquiv : Carrier p ≃+* Carrier p where
  __ := frobeniusHom p
  invFun := inverseHom p
  left_inv x := Subtype.ext ((productEquiv p).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((productEquiv p).apply_symm_apply x.val)

theorem frobenius_continuous : Continuous (frobeniusEquiv p) :=
  ((productEquiv_continuous p).comp continuous_subtype_val).subtype_mk _

theorem inverse_continuous : Continuous (frobeniusEquiv p).symm :=
  ((productEquiv_symm_continuous p).comp continuous_subtype_val).subtype_mk _

theorem frobenius_inclusion (x : Ring p) :
    frobeniusEquiv p (inclusion p x) = inclusion p (PadicWittRhoFrobenius.frobeniusEquiv p x) :=
  Subtype.ext (productEquiv_diagonal p x)

theorem inverse_inclusion (x : Ring p) :
    (frobeniusEquiv p).symm (inclusion p x) =
      inclusion p ((PadicWittRhoFrobenius.frobeniusEquiv p).symm x) :=
  Subtype.ext (productEquiv_symm_diagonal p x)

theorem evaluate_frobenius (ρ : PadicWittRhoCompletion.Radius) (x : Carrier p) :
    evaluate p (poweredRadius p ρ) (frobeniusEquiv p x) =
      completedEquiv p ρ (evaluate p ρ x) :=
  productEquiv_powered p x.val ρ

theorem evaluate_inverse (ρ : PadicWittRhoCompletion.Radius) (x : Carrier p) :
    evaluate p ρ ((frobeniusEquiv p).symm x) =
      (completedEquiv p ρ).symm (evaluate p (poweredRadius p ρ) x) := rfl

theorem coordinateSeminorm_frobenius (ρ : PadicWittRhoCompletion.Radius) (x : Carrier p) :
    coordinateSeminorm p (poweredRadius p ρ) (frobeniusEquiv p x) =
      coordinateSeminorm p ρ x ^ p := by
  change ‖evaluate p (poweredRadius p ρ) (frobeniusEquiv p x)‖ =
    ‖evaluate p ρ x‖ ^ p
  rw [evaluate_frobenius, completedEquiv_apply, completedHom_norm]

theorem coordinateSeminorm_inverse (ρ : PadicWittRhoCompletion.Radius) (x : Carrier p) :
    coordinateSeminorm p ρ ((frobeniusEquiv p).symm x) ^ p =
      coordinateSeminorm p (poweredRadius p ρ) x := by
  change ‖evaluate p ρ ((frobeniusEquiv p).symm x)‖ ^ p =
    ‖evaluate p (poweredRadius p ρ) x‖
  rw [evaluate_inverse, completedEquiv_inverse_norm]

def frobeniusHomeomorph : Carrier p ≃ₜ Carrier p where
  toEquiv := (frobeniusEquiv p).toEquiv
  continuous_toFun := frobenius_continuous p
  continuous_invFun := inverse_continuous p

end
end JoshiTeich.Act1Scene1.PadicWittAllRadiusFrobenius
