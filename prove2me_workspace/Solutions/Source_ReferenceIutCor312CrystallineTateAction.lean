import Solutions.Source_ReferenceIutCor312CrystallineTateLocalization
import Solutions.Source_ReferenceIutCor312CrystallineAction
import Mathlib.Algebra.Ring.Aut

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open CrystallineEnvelope LocalKummer

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "Ω" => Algebraic K
local notation "C" => Field K
local notation "G" => (Ω ≃ₐ[K] Ω)
local notation "ι" => (UniformSpace.Completion.coeRingHom : Ω →+* C)
local notation "B" => ACrisInvertP C p
local notation "Bₜ" => ACrisInvertTatePeriod C p ι
local notation "t" => mappedTateBasisPeriod C p ι
local notation "j" => algebraMap B Bₜ

private theorem extendGaloisACrisInvertTatePeriodHom_one :
    extendGaloisACrisInvertTatePeriodHom p (1 : G) = RingHom.id Bₜ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers t) (RingHom.ext fun z => ?_)
  simp only [RingHom.comp_apply, RingHom.id_apply,
    extendGaloisACrisInvertTatePeriodHom_algebraMap, extendGaloisACrisInvertP_one_apply]

private theorem extendGaloisACrisInvertTatePeriodHom_mul (σ τ : G) :
    extendGaloisACrisInvertTatePeriodHom p (σ * τ) =
      (extendGaloisACrisInvertTatePeriodHom p σ).comp
        (extendGaloisACrisInvertTatePeriodHom p τ) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers t) (RingHom.ext fun z => ?_)
  simp only [RingHom.comp_apply, extendGaloisACrisInvertTatePeriodHom_algebraMap,
    extendGaloisACrisInvertP_mul_apply]

private theorem galoisHom_comp_inv (σ : G) :
    (extendGaloisACrisInvertTatePeriodHom p σ).comp
      (extendGaloisACrisInvertTatePeriodHom p σ⁻¹) = RingHom.id Bₜ :=
  (extendGaloisACrisInvertTatePeriodHom_mul p σ σ⁻¹).symm.trans
    ((congrArg (extendGaloisACrisInvertTatePeriodHom p) (mul_inv_cancel σ)).trans
      (extendGaloisACrisInvertTatePeriodHom_one (K := K) p))

private theorem galoisHom_inv_comp (σ : G) :
    (extendGaloisACrisInvertTatePeriodHom p σ⁻¹).comp
      (extendGaloisACrisInvertTatePeriodHom p σ) = RingHom.id Bₜ :=
  (extendGaloisACrisInvertTatePeriodHom_mul p σ⁻¹ σ).symm.trans
    ((congrArg (extendGaloisACrisInvertTatePeriodHom p) (inv_mul_cancel σ)).trans
      (extendGaloisACrisInvertTatePeriodHom_one (K := K) p))

/-- The automorphism induced by the given Galois element after inverting the
original Tate period. -/
def extendGaloisACrisInvertTatePeriod (σ : G) : Bₜ ≃+* Bₜ :=
  RingEquiv.ofRingHom (R := Bₜ) (S := Bₜ) (extendGaloisACrisInvertTatePeriodHom p σ)
    (extendGaloisACrisInvertTatePeriodHom p σ⁻¹) (galoisHom_comp_inv p σ) (galoisHom_inv_comp p σ)

/-- The actual Galois action on the crystalline ring with the Tate period inverted. -/
def galoisACrisInvertTatePeriod : G →* RingAut Bₜ where
  toFun := extendGaloisACrisInvertTatePeriod p
  map_one' := by
    apply RingEquiv.ext
    intro z
    change extendGaloisACrisInvertTatePeriodHom p (1 : G) z = z
    exact RingHom.congr_fun (extendGaloisACrisInvertTatePeriodHom_one (K := K) p) z
  map_mul' σ τ := by
    apply RingEquiv.ext
    intro z
    change extendGaloisACrisInvertTatePeriodHom p (σ * τ) z =
      extendGaloisACrisInvertTatePeriodHom p σ (extendGaloisACrisInvertTatePeriodHom p τ z)
    exact RingHom.congr_fun (extendGaloisACrisInvertTatePeriodHom_mul p σ τ) z

@[simp]
theorem extendGaloisACrisInvertTatePeriod_algebraMap (σ : G) (z : B) :
    extendGaloisACrisInvertTatePeriod p σ (j z) =
      j (mapACrisInvertP C p (extendGaloisACris p σ) z) :=
  extendGaloisACrisInvertTatePeriodHom_algebraMap p σ z

theorem extendGaloisACrisInvertTatePeriod_mappedTateBasisPeriod (σ : G) :
    extendGaloisACrisInvertTatePeriod p σ (j t) =
      j (padicIntMapACrisInvertP p C (Cyclotomic.character p σ : PadicInt p)) * j t := by
  let a : B := padicIntMapACrisInvertP p C (Cyclotomic.character p σ : PadicInt p)
  exact (extendGaloisACrisInvertTatePeriod_algebraMap p σ t).trans
    ((congrArg (j : B →+* Bₜ)
      (extendGaloisACrisInvertP_mappedTateBasisPeriod p σ)).trans (map_mul (j : B →+* Bₜ) a t))

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
