import Solutions.Source_ReferenceIutCor312PreTiltUntiltComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.WittRingEquiv

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.GeometricTiltComparison

open JoshiTeich.Prologue

noncomputable section

variable {C C' : Type*} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable [NormedField C'] [IsUltrametricDist C'] [CompleteSpace C']
variable (e : C ≃+* C') (d : ℕ) (hd : 0 < d) (hnorm : ∀ x : C, ‖e x‖ ^ d = ‖x‖)
variable (p : ℕ) [Fact p.Prime]
variable [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable [Fact (0 < ‖(p : C')‖ ∧ ‖(p : C')‖ < 1)]

local notation "𝒪" => LocalGeometricFontaine.integerRing C
local notation "𝒪'" => LocalGeometricFontaine.integerRing C'
local notation "𝔭'" => Ideal.span {(p : 𝒪')}
local notation "𝔸" => WittVector p (GeometricTiltField.Source C p)
local notation "𝔸'" => WittVector p (GeometricTiltField.Source C' p)
local notation "θ" => (Perfectoid.thetaMap (O := 𝒪) (p := p))
local notation "θ'" => (Perfectoid.thetaMap (O := 𝒪') (p := p))

/-- The Witt-vector comparison intertwines the two canonical Fontaine maps. -/
theorem thetaMap_mapEquiv (x : 𝔸) :
    θ' (WittRingEquiv.mapEquiv p (preTiltEquiv e d hd hnorm p) x) =
      integerEquiv e d hd hnorm (θ x) := by
  let w : 𝔸 ≃+* 𝔸' := WittRingEquiv.mapEquiv p (preTiltEquiv e d hd hnorm p)
  let r : 𝒪 ≃+* 𝒪' := integerEquiv e d hd hnorm
  let thetaSource : 𝔸 →+* 𝒪 := θ
  let thetaTarget : 𝔸' →+* 𝒪' := θ'
  change thetaTarget (w x) = r (thetaSource x)
  apply (IsHausdorff.eq_iff_smodEq (I := 𝔭')).mpr
  intro n
  rw [smul_eq_mul, Ideal.mul_top, SModEq.idealQuotientMk]
  let q := Ideal.Quotient.mk (𝔭' ^ n)
  have hnil : IsNilpotent (p : 𝒪' ⧸ 𝔭' ^ n) := by
    refine ⟨n, ?_⟩
    rw [← map_natCast q p, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (p : 𝒪')) n
  have hquotient := WittVector.eq_of_apply_teichmuller_eq
    (q.comp (thetaTarget.comp w.toRingHom)) (q.comp (r.toRingHom.comp thetaSource)) hnil (by
      intro y
      change q (θ' (WittRingEquiv.mapEquiv p (preTiltEquiv e d hd hnorm p)
        (WittVector.teichmuller p y))) = q (r (θ (WittVector.teichmuller p y)))
      rw [WittRingEquiv.mapEquiv_teichmuller, Perfectoid.thetaMap_teichmuller,
        Perfectoid.thetaMap_teichmuller]
      exact congrArg q (untilt_preTiltEquiv e d hd hnorm p y))
  exact DFunLike.congr_fun hquotient x

/-- The comparison carries the source Fontaine kernel onto the target kernel. -/
theorem mapEquiv_mem_thetaKernel_iff (x : 𝔸) :
    WittRingEquiv.mapEquiv p (preTiltEquiv e d hd hnorm p) x ∈ RingHom.ker θ' ↔
      x ∈ RingHom.ker θ := by
  simp only [RingHom.mem_ker, thetaMap_mapEquiv]
  simpa only [map_zero] using
    (integerEquiv e d hd hnorm).injective.eq_iff (a := θ x) (b := (0 : 𝒪))

end

end JoshiTeich.Act1Scene1.GeometricTiltComparison
