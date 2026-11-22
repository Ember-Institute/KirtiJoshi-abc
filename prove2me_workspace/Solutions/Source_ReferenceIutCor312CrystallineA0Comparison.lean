import Solutions.Source_ReferenceIutCor312CrystallineA0Map
import Solutions.Source_ReferenceIutCor312FontaineComparison

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue GeometricTiltComparison

noncomputable section

variable {C C' : Type*} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable [NormedField C'] [IsUltrametricDist C'] [CompleteSpace C']
variable (p : ℕ) [Fact p.Prime]
variable [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable [Fact (0 < ‖(p : C')‖ ∧ ‖(p : C')‖ < 1)]
variable (e : C ≃+* C') (d : ℕ) (hd : 0 < d) (hnorm : ∀ x : C, ‖e x‖ ^ d = ‖x‖)

local notation "ι" => algebraMap (Ainf C p) (AinfInvertP C p)
local notation "ι'" => algebraMap (Ainf C' p) (AinfInvertP C' p)
local notation "θ" =>
  (Perfectoid.thetaMap (O := LocalGeometricFontaine.integerRing C) (p := p))
local notation "θ'" =>
  (Perfectoid.thetaMap (O := LocalGeometricFontaine.integerRing C') (p := p))
local notation "τ" => preTiltEquiv e d hd hnorm p
local notation "𝓌" => WittRingEquiv.mapEquiv p τ
local notation "𝓁" => WittRingEquiv.invertPrimeEquiv p τ

theorem invertPrimeEquiv_gamma (n : ℕ) (x : Ainf C p) :
    𝓁 (gamma C p n x) = gamma C' p n (𝓌 x) :=
  map_gamma_of_algebraMap p (𝓌).toRingHom (𝓁).toRingHom
    (WittRingEquiv.invertPrimeEquiv_algebraMap p τ) n x

private theorem invertPrimeEquiv_symm_algebraMap (x : Ainf C' p) :
    (𝓁).symm (ι' x) = ι ((𝓌).symm x) := by
  apply (𝓁).injective
  rw [RingEquiv.apply_symm_apply, WittRingEquiv.invertPrimeEquiv_algebraMap,
    RingEquiv.apply_symm_apply]

private theorem invertPrimeEquiv_mem_A0_iff (x : AinfInvertP C p) :
    x ∈ A0 C p ↔ 𝓁 x ∈ A0 C' p := by
  constructor
  · exact map_mem_A0_of_algebraMap p (𝓌).toRingHom (𝓁).toRingHom
      (WittRingEquiv.invertPrimeEquiv_algebraMap p τ)
      (fun y hy => (mapEquiv_mem_thetaKernel_iff e d hd hnorm p y).mpr hy) x
  · intro hx
    have hker (y : Ainf C' p) (hy : y ∈ RingHom.ker θ') :
        (𝓌).symm y ∈ RingHom.ker θ :=
      (mapEquiv_mem_thetaKernel_iff e d hd hnorm p ((𝓌).symm y)).mp (by
        simpa only [RingEquiv.apply_symm_apply] using hy)
    have hx' := map_mem_A0_of_algebraMap p (𝓌).symm.toRingHom (𝓁).symm.toRingHom
      (invertPrimeEquiv_symm_algebraMap p e d hd hnorm) hker (𝓁 x) hx
    change (𝓁).symm (𝓁 x) ∈ A0 C p at hx'
    rw [RingEquiv.symm_apply_apply] at hx'
    exact hx'

/-- The comparison of the localized Witt rings restricts to the
integral divided-power subalgebras. -/
def equivA0 : A0 C p ≃+* A0 C' p :=
  (𝓁).restrict (A0 C p) (A0 C' p) (invertPrimeEquiv_mem_A0_iff p e d hd hnorm)

theorem equivA0_coe (x : A0 C p) :
    (equivA0 p e d hd hnorm x : AinfInvertP C' p) = 𝓁 (x : AinfInvertP C p) :=
  rfl

@[simp]
theorem equivA0_algebraMap (x : Ainf C p) :
    equivA0 p e d hd hnorm (algebraMap (Ainf C p) (A0 C p) x) =
      algebraMap (Ainf C' p) (A0 C' p) (𝓌 x) := by
  apply Subtype.ext
  exact WittRingEquiv.invertPrimeEquiv_algebraMap p τ x

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
