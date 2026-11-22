import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltComparison
import Solutions.Source_ReferenceIutCor312FontaineGalois

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open JoshiTeich.Prologue GeometricTiltComparison

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable {C : Type*} [NormedField C] [IsUltrametricDist C]
variable (p : ℕ) [Fact p.Prime]
variable [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]
variable [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable (e : Field K ≃+* C) (d : ℕ) (hd : 0 < d)
variable (hnorm : ∀ x : Field K, ‖e x‖ ^ d = ‖x‖)
variable (σ : Algebraic K ≃ₐ[K] Algebraic K)
variable (g : C ≃+* C) (hg : ∀ x : C, ‖g x‖ ^ (1 : ℕ) = ‖x‖)
variable (hcomm : ∀ x : Field K, e (extendGalois σ x) = g (e x))

local notation "𝒪" => LocalGeometricFontaine.integerRing (Field K)
local notation "𝒯" => GeometricTiltField.Source (Field K) p
local notation "τ" => preTiltEquiv e d hd hnorm p
local notation "τg" => preTiltEquiv g 1 Nat.one_pos hg p

include hcomm

private theorem integerEquiv_extendGaloisIntegers (x : 𝒪) :
    integerEquiv e d hd hnorm (extendGaloisIntegers σ x) =
      integerEquiv g 1 Nat.one_pos hg (integerEquiv e d hd hnorm x) := by
  apply Subtype.ext
  exact hcomm x

private theorem modPEquiv_extendGaloisModP (x : ModP 𝒪 p) :
    modPEquiv e d hd hnorm p (extendGaloisModP p σ x) =
      modPEquiv g 1 Nat.one_pos hg p (modPEquiv e d hd hnorm p x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [extendGaloisModP_mk, modPEquiv_mk]
  exact congrArg (Ideal.Quotient.mk (Ideal.span {(p : LocalGeometricFontaine.integerRing C)}))
    (integerEquiv_extendGaloisIntegers e d hd hnorm σ g hg hcomm x)

/-- The norm-power comparison intertwines the original Galois action
on the pretilt with the action induced by the target field automorphism. -/
theorem preTiltEquiv_extendGaloisPreTilt (x : 𝒯) :
    τ (extendGaloisPreTilt p σ x) = τg (τ x) := by
  apply Perfection.ext
  intro n
  change PreTilt.coeff n (τ (extendGaloisPreTilt p σ x)) =
    PreTilt.coeff n (τg (τ x))
  simp only [preTiltEquiv_coeff, coeff_extendGaloisPreTilt]
  exact modPEquiv_extendGaloisModP p e d hd hnorm σ g hg hcomm (PreTilt.coeff n x)

/-- The Witt-vector comparison intertwines the Galois actions. -/
theorem wittEquiv_extendGaloisFontaine (x : WittVector p 𝒯) :
    WittRingEquiv.mapEquiv p τ (extendGaloisFontaine p σ x) =
      WittRingEquiv.mapEquiv p τg (WittRingEquiv.mapEquiv p τ x) := by
  apply WittVector.ext
  intro n
  simp only [WittRingEquiv.mapEquiv_coeff, coeff_extendGaloisFontaine]
  exact preTiltEquiv_extendGaloisPreTilt p e d hd hnorm σ g hg hcomm (x.coeff n)

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
