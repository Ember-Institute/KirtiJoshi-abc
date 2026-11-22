import Solutions.Source_ReferenceIutCor312PreTiltGalois
import ArithmeticTeichmullerSpaces.Act1Scene1.WittRingEquiv

/-!
For Joshi III §9.6, the completed Galois automorphisms commute with the
canonical Fontaine map and therefore preserve its kernel on the Witt ring
of the pretilt of the completed algebraic closure.
-/

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open JoshiTeich.Prologue

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "𝒪" => LocalGeometricFontaine.integerRing (Field K)
local notation "𝔭" => Ideal.span {(p : 𝒪)}
local notation "𝒯" => GeometricTiltField.Source (Field K) p
local notation "𝔸" => WittVector p 𝒯

/-- The untilt commutes with the automorphisms of the completed valuation ring. -/
theorem untilt_extendGaloisPreTilt (σ : Algebraic K ≃ₐ[K] Algebraic K) (x : 𝒯) :
    PreTilt.untilt (extendGaloisPreTilt p σ x) = extendGaloisIntegers σ (PreTilt.untilt x) := by
  change Perfection.teichmuller p 𝔭 (extendGaloisPreTilt p σ x) =
    extendGaloisIntegers σ (PreTilt.untilt x)
  apply Perfection.teichmuller_spec
  intro n
  let y := ((frobeniusEquiv 𝒯 p).symm^[n]) x
  have hcoeff : PreTilt.coeff 0 y = PreTilt.coeff n x := by
    simpa only [Nat.zero_add] using PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n x
  have hpow : PreTilt.untilt y ^ (p ^ n) = PreTilt.untilt x :=
    PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n
  refine ⟨extendGaloisIntegers σ (PreTilt.untilt y), ?_, ?_⟩
  · rw [← extendGaloisModP_mk, PreTilt.mk_untilt_eq_coeff_zero, coeff_extendGaloisPreTilt]
    exact congrArg (extendGaloisModP p σ) hcoeff
  · rw [← map_pow, hpow, SModEq.idealQuotientMk]

private def extendGaloisPreTiltEquiv (σ : Algebraic K ≃ₐ[K] Algebraic K) : 𝒯 ≃+* 𝒯 where
  __ := extendGaloisPreTilt p σ
  invFun := Perfection.map p (extendGaloisModP p σ).symm.toRingHom
  left_inv x := by
    apply Perfection.ext
    intro n
    change (extendGaloisModP p σ).symm
      (extendGaloisModP p σ (Perfection.coeff (ModP 𝒪 p) p n x)) = _
    exact (extendGaloisModP p σ).symm_apply_apply _
  right_inv x := by
    apply Perfection.ext
    intro n
    change extendGaloisModP p σ
      ((extendGaloisModP p σ).symm (Perfection.coeff (ModP 𝒪 p) p n x)) = _
    exact (extendGaloisModP p σ).apply_symm_apply _

/-- The automorphism of the Fontaine Witt ring induced by an algebraic Galois automorphism. -/
def extendGaloisFontaine (σ : Algebraic K ≃ₐ[K] Algebraic K) : 𝔸 ≃+* 𝔸 :=
  WittRingEquiv.mapEquiv p (extendGaloisPreTiltEquiv p σ)

theorem coeff_extendGaloisFontaine (σ : Algebraic K ≃ₐ[K] Algebraic K)
    (x : 𝔸) (n : ℕ) :
    (extendGaloisFontaine p σ x).coeff n = extendGaloisPreTilt p σ (x.coeff n) :=
  rfl

theorem extendGaloisFontaine_teichmuller (σ : Algebraic K ≃ₐ[K] Algebraic K) (x : 𝒯) :
    extendGaloisFontaine p σ (WittVector.teichmuller p x) =
      WittVector.teichmuller p (extendGaloisPreTilt p σ x) :=
  WittRingEquiv.mapEquiv_teichmuller p (extendGaloisPreTiltEquiv p σ) x

/-- Fontaine's map intertwines the Witt and valuation-ring Galois automorphisms. -/
theorem thetaMap_extendGaloisFontaine (σ : Algebraic K ≃ₐ[K] Algebraic K) (x : 𝔸) :
    Perfectoid.thetaMap (p := p) (extendGaloisFontaine p σ x) =
      extendGaloisIntegers σ (Perfectoid.thetaMap (p := p) x) := by
  let θ : 𝔸 →+* 𝒪 := Perfectoid.thetaMap (p := p)
  change θ (extendGaloisFontaine p σ x) = extendGaloisIntegers σ (θ x)
  apply (IsHausdorff.eq_iff_smodEq (I := 𝔭)).mpr
  intro n
  rw [smul_eq_mul, Ideal.mul_top, SModEq.idealQuotientMk]
  let q := Ideal.Quotient.mk (𝔭 ^ n)
  have hnil : IsNilpotent (p : 𝒪 ⧸ 𝔭 ^ n) := by
    refine ⟨n, ?_⟩
    rw [← map_natCast q p, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (p : 𝒪)) n
  have heq := WittVector.eq_of_apply_teichmuller_eq
    (q.comp (θ.comp (extendGaloisFontaine p σ).toRingHom))
    (q.comp ((extendGaloisIntegers σ).toRingHom.comp θ)) hnil (by
      intro y
      change q (Perfectoid.thetaMap (p := p) (extendGaloisFontaine p σ (WittVector.teichmuller p y))) =
        q (extendGaloisIntegers σ (Perfectoid.thetaMap (p := p) (WittVector.teichmuller p y)))
      rw [extendGaloisFontaine_teichmuller, Perfectoid.thetaMap_teichmuller,
        Perfectoid.thetaMap_teichmuller]
      exact congrArg q (untilt_extendGaloisPreTilt p σ y))
  exact DFunLike.congr_fun heq x

theorem extendGaloisFontaine_mem_thetaKernel_iff (σ : Algebraic K ≃ₐ[K] Algebraic K) (x : 𝔸) :
    extendGaloisFontaine p σ x ∈ RingHom.ker (Perfectoid.thetaMap (O := 𝒪) (p := p)) ↔
      x ∈ RingHom.ker (Perfectoid.thetaMap (O := 𝒪) (p := p)) := by
  simp only [RingHom.mem_ker, thetaMap_extendGaloisFontaine]
  simpa only [map_zero] using
    (extendGaloisIntegers σ).injective.eq_iff
      (a := Perfectoid.thetaMap (p := p) x) (b := (0 : 𝒪))

end
end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
