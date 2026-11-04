import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittFrechetComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAllRadiusFrobenius

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-FRECHET-FROBENIUS
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`.
fidelity: transports the independent standard all-radius Frobenius to the
existing Hausdorff completion of the standard bounded Witt ring. It proves
forward and inverse continuity, compatibility with the original inclusion,
and exact radius-map and norm identities for the original family of radii.
Only p and its primality instance enter the construction.
Original proofs using the project's completion comparison pattern;
no reference implementation copied.
boundary: Scene1/Derived; scalar algebra, paper source identities,
Tate-log convergence and period comparisons remain separate. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.PadicWittFrechetFrobenius

open PadicWittFrechetComparison
open PadicWittRhoFrobeniusCompletion
open scoped Topology
noncomputable section

variable (p : ℕ) [Fact p.Prime]

abbrev Completed := PadicWittFrechetComparison.Completed p
abbrev Radius := PadicWittRhoCompletion.Radius

def frobeniusEquiv : Completed p ≃+* Completed p :=
  (ringEquiv p).trans ((PadicWittAllRadiusFrobenius.frobeniusEquiv p).trans
    (ringEquiv p).symm)

theorem frobeniusEquiv_apply (x : Completed p) :
    ringEquiv p (frobeniusEquiv p x) =
      PadicWittAllRadiusFrobenius.frobeniusEquiv p (ringEquiv p x) := by
  simp [frobeniusEquiv]

theorem frobeniusEquiv_symm_apply (x : Completed p) :
    ringEquiv p ((frobeniusEquiv p).symm x) =
      (PadicWittAllRadiusFrobenius.frobeniusEquiv p).symm (ringEquiv p x) := by
  apply (PadicWittAllRadiusFrobenius.frobeniusEquiv p).injective
  rw [← frobeniusEquiv_apply, RingEquiv.apply_symm_apply,
    RingEquiv.apply_symm_apply]

theorem frobeniusEquiv_continuous : Continuous (frobeniusEquiv p) := by
  exact (ringEquiv_symm_continuous p).comp <|
    (PadicWittAllRadiusFrobenius.frobenius_continuous p).comp
      (ringEquiv_continuous p)

theorem frobeniusEquiv_symm_continuous : Continuous (frobeniusEquiv p).symm := by
  change Continuous (fun x =>
    (ringEquiv p).symm
      ((PadicWittAllRadiusFrobenius.frobeniusEquiv p).symm (ringEquiv p x)))
  exact (ringEquiv_symm_continuous p).comp <|
    (PadicWittAllRadiusFrobenius.inverse_continuous p).comp
      (ringEquiv_continuous p)

theorem frobenius_originalInclusion (x : PadicBoundedWittLocalization.Ring p) :
    frobeniusEquiv p (originalInclusion p x) =
      originalInclusion p (PadicWittRhoFrobenius.frobeniusEquiv p x) := by
  apply (ringEquiv p).injective
  rw [frobeniusEquiv_apply, ringEquiv_originalInclusion,
    PadicWittAllRadiusFrobenius.frobenius_inclusion, ringEquiv_originalInclusion]

theorem inverse_originalInclusion (x : PadicBoundedWittLocalization.Ring p) :
    (frobeniusEquiv p).symm (originalInclusion p x) =
      originalInclusion p ((PadicWittRhoFrobenius.frobeniusEquiv p).symm x) := by
  apply (ringEquiv p).injective
  rw [frobeniusEquiv_symm_apply, ringEquiv_originalInclusion,
    PadicWittAllRadiusFrobenius.inverse_inclusion, ringEquiv_originalInclusion]

theorem radiusMap_frobenius (ρ : Radius) (x : Completed p) :
    radiusMap p (poweredRadius p ρ) (frobeniusEquiv p x) =
      completedEquiv p ρ (radiusMap p ρ x) := by
  change PadicWittAllRadiusCompletion.evaluate p (poweredRadius p ρ)
    (ringEquiv p (frobeniusEquiv p x)) =
      completedEquiv p ρ (PadicWittAllRadiusCompletion.evaluate p ρ (ringEquiv p x))
  rw [frobeniusEquiv_apply, PadicWittAllRadiusFrobenius.evaluate_frobenius]

theorem radiusMap_inverse (ρ : Radius) (x : Completed p) :
    radiusMap p ρ ((frobeniusEquiv p).symm x) =
      (completedEquiv p ρ).symm (radiusMap p (poweredRadius p ρ) x) := by
  change PadicWittAllRadiusCompletion.evaluate p ρ
    (ringEquiv p ((frobeniusEquiv p).symm x)) =
      (completedEquiv p ρ).symm
        (PadicWittAllRadiusCompletion.evaluate p (poweredRadius p ρ) (ringEquiv p x))
  rw [frobeniusEquiv_symm_apply, PadicWittAllRadiusFrobenius.evaluate_inverse]

theorem norm_radiusMap_frobenius (ρ : Radius) (x : Completed p) :
    ‖radiusMap p (poweredRadius p ρ) (frobeniusEquiv p x)‖ =
      ‖radiusMap p ρ x‖ ^ p := by
  rw [radiusMap_frobenius, completedEquiv_norm]

theorem norm_radiusMap_inverse (ρ : Radius) (x : Completed p) :
    ‖radiusMap p ρ ((frobeniusEquiv p).symm x)‖ ^ p =
      ‖radiusMap p (poweredRadius p ρ) x‖ := by
  rw [radiusMap_inverse, completedEquiv_inverse_norm]

def frobeniusHomeomorph : Completed p ≃ₜ Completed p where
  toEquiv := (frobeniusEquiv p).toEquiv
  continuous_toFun := frobeniusEquiv_continuous p
  continuous_invFun := frobeniusEquiv_symm_continuous p

end
end JoshiTeich.Act1Scene1.PadicWittFrechetFrobenius
