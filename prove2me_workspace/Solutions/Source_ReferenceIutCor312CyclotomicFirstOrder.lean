import Solutions.Source_ReferenceIutCor312CrystallineInputs
import Solutions.Source_ReferenceIutCor312CrystallineFontaineKernel
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerPrimitiveTower
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue
open scoped BigOperators

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "𝒪" => LocalGeometricFontaine.integerRing C
local notation "k" => IsLocalRing.ResidueField 𝒪
local notation "ρ" => IsLocalRing.residue 𝒪
local notation "θ" => (Perfectoid.thetaMap (O := 𝒪) (p := p))
local notation "ξ" => fontainePrimitive C p

omit [CompleteSpace C] [IsAlgClosed C] [Fact p.Prime] in
private theorem residue_prime : ρ (p : 𝒪) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact LocalGeometricFontaine.prime_nonunit C p

private def quotientResidue : ModP 𝒪 p →+* k :=
  Ideal.Quotient.lift _ ρ (by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul, residue_prime C p, zero_mul])

private def tiltResidue : GeometricTiltField.Source C p →+* k :=
  (quotientResidue C p).comp (PreTilt.coeff 0)

private theorem tiltResidue_eq_untilt (x : GeometricTiltField.Source C p) :
    tiltResidue C p x = ρ (PreTilt.untilt x) := by
  change quotientResidue C p (PreTilt.coeff 0 x) = _
  rw [← PreTilt.mk_untilt_eq_coeff_zero, quotientResidue, Ideal.Quotient.lift_mk]

local notation "rW" => WittVector.map (tiltResidue C p)

private theorem residue_fontainePrimitive : rW ξ = -(p : WittVector p k) := by
  have hp : tiltResidue C p (primeTilt C p) = 0 := by
    rw [tiltResidue_eq_untilt, primeTilt, GeometricTiltSharp.untilt_rootLift, residue_prime]
  simp only [fontainePrimitive, map_sub, map_natCast, WittVector.map_teichmuller,
    hp, WittVector.teichmuller_zero, zero_sub]

private theorem residue_coeff_zero_of_theta_zero (x : Ainf C p) (hx : θ x = 0) :
    (rW x).coeff 0 = 0 := by
  rw [WittVector.map_coeff]
  change quotientResidue C p (PreTilt.coeff 0 (x.coeff 0)) = 0
  rw [← WittVector.mk_fontaineTheta]
  change quotientResidue C p (Ideal.Quotient.mk _ (θ x)) = 0
  rw [hx, map_zero, map_zero]

/-- The cyclotomic Teichmüller difference has nonzero first-order coordinate
if the first root in the original tower is nontrivial. -/
theorem cyclotomicTeichmuller_exists_firstOrder (ε : LocalKummer.cyclotomicTateGroup p C)
    (hε : ε.1 1 ≠ 1) :
    ∃ b : Ainf C p, θ b ≠ 0 ∧
      WittVector.teichmuller p (CyclotomicTateTilt.toPreTilt C p ε) - 1 = ξ * b := by
  letI : CharP k p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
      ((map_natCast ρ p).symm.trans (residue_prime C p))
  let a := CyclotomicTateTilt.toPreTilt C p ε
  let s := (frobeniusEquiv (GeometricTiltField.Source C p) p).symm a
  let β := WittVector.teichmuller p s
  let ζ := CyclotomicTateTilt.coordinate C p ε 1
  have hβp : β ^ p = WittVector.teichmuller p a := by
    dsimp only [β, s]
    rw [← map_pow, frobeniusEquiv_symm_pow_p]
  have hs : PreTilt.untilt s = ζ := by
    simpa only [s, a, ζ, Function.iterate_one] using
      (CyclotomicTateTilt.untilt_shift_toPreTilt C p ε 1)
  have hβθ : θ β = ζ := (Perfectoid.thetaMap_teichmuller s).trans hs
  have hζ : ζ - 1 ≠ 0 := by
    intro h
    apply hε
    apply Units.ext
    exact congrArg (fun x : 𝒪 => (x : C)) (sub_eq_zero.mp h)
  have hζpow : ζ ^ p = 1 :=
    (CyclotomicTateTilt.coordinate_succ C p ε 0).trans
      (CyclotomicTateTilt.coordinate_zero C p ε)
  have hrζ : ρ ζ = 1 := by
    apply sub_eq_zero.mp
    apply eq_zero_of_pow_eq_zero (n := p)
    rw [sub_pow_char, one_pow, ← map_pow, hζpow, map_one, sub_self]
  have hrβ : rW β = 1 := by
    dsimp only [β]
    rw [WittVector.map_teichmuller, tiltResidue_eq_untilt, hs, hrζ, map_one]
  let e : Ainf C p := ∑ i ∈ Finset.range p, β ^ i
  have he : e * (β - 1) = WittVector.teichmuller p a - 1 := by
    dsimp only [e]
    rw [geom_sum_mul, hβp]
  have hξe : e ∈ RingHom.ker θ := by
    have h := congrArg θ he
    rw [map_mul, map_sub θ β, hβθ, map_one θ,
      RingHom.mem_ker.mp (LocalKummer.RootTower.cyclotomic_teichmuller_sub_one_mem_theta_ker ε)] at h
    exact RingHom.mem_ker.mpr ((mul_eq_zero.mp h).resolve_right hζ)
  rw [fontaineKernel_eq_span C p, Ideal.mem_span_singleton] at hξe
  obtain ⟨b, hb⟩ := hξe
  have hbθ : θ b ≠ 0 := by
    intro h
    have hre : rW e = (p : WittVector p k) := by
      simp [e, map_sum, map_pow, hrβ]
    have hbmap := congrArg rW hb
    rw [hre, map_mul, residue_fontainePrimitive] at hbmap
    have hz : (rW b + 1) * (p : WittVector p k) = 0 := by
      calc
        _ = (p : WittVector p k) - (-(p : WittVector p k)) * rW b := by ring
        _ = 0 := by rw [← hbmap, sub_self]
    have hsum := (mul_eq_zero.mp hz).resolve_right (WittVector.p_nonzero p k)
    have hcoeff := congrArg (fun z : WittVector p k => WittVector.constantCoeff z) hsum
    simp only [map_add, map_one, map_zero] at hcoeff
    change (rW b).coeff 0 + 1 = 0 at hcoeff
    rw [residue_coeff_zero_of_theta_zero C p b h, zero_add] at hcoeff
    exact one_ne_zero hcoeff
  refine ⟨b * (β - 1), ?_, ?_⟩
  · rw [map_mul, map_sub, hβθ, map_one]
    exact mul_ne_zero hbθ hζ
  · change WittVector.teichmuller p a - 1 = ξ * (b * (β - 1))
    rw [← he, hb, mul_assoc]

variable [CharZero C]

/-- The primitive compatible tower already used for the Tate basis has a
nonzero first-order crystalline coordinate. -/
theorem tateBasisGenerator_exists_firstOrder :
    ∃ b : Ainf C p, θ b ≠ 0 ∧
      WittVector.teichmuller p (CyclotomicTateTilt.toPreTilt C p
        (LocalKummer.TateBasis.generator (p := p) (Ω := C))) - 1 = ξ * b := by
  apply cyclotomicTeichmuller_exists_firstOrder C p
  exact (LocalKummer.TateBasis.generator_isPrimitive (p := p) (Ω := C) 1).ne_one
    (by simpa only [pow_one] using (Fact.out : p.Prime).one_lt)

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
