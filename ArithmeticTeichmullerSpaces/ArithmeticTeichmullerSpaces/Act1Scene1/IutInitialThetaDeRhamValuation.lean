import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDeRhamField
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
source-id: JT-SCENE1-INITIAL-THETA-DE-RHAM-VALUATION
source: Joshi II eta_K and primitive kernel (838, 932), the inclusions into
B_dR (1069--1076); Joshi III local Hodge rings; Mathlib DVR adic valuation.
fidelity: equips the same actual BDeRham with the normalized discrete valuation
of its actual BDeRhamPlus maximal ideal. Identifies the original plus ring with
the valuation integers and transports the same theta to them, including its
kernel, residue quotient and the primitive-power filtration.
This is the primitive-adic valuation, with no Frechet/rho norm or theta-locus
identity asserted. Original proofs; no reference-engine copy; R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation

open JoshiTeich.Prologue InitialThetaDeRhamCompletion InitialThetaDeRhamField
open scoped WithZero
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance primeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w

def valuation : Valuation (Carrier D w) ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal (Ring D w)).valuation (Carrier D w)

instance discrete : (valuation D w).IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete (Ring D w) (Carrier D w)

theorem valuation_surjective : Function.Surjective (valuation D w) :=
  (IsDiscreteValuationRing.maximalIdeal (Ring D w)).valuation_surjective (Carrier D w)

theorem integers : (valuation D w).Integers (Ring D w) where
  hom_inj := InitialThetaDeRhamField.algebraMap_injective D w
  map_le_one := (IsDiscreteValuationRing.maximalIdeal (Ring D w)).valuation_le_one
  exists_of_le_one := by
    intro r hr
    exact IsDiscreteValuationRing.exists_lift_of_le_one hr

theorem valuation_le_one_iff (x : Carrier D w) :
    valuation D w x ≤ 1 ↔ ∃ a : Ring D w, algebraMap (Ring D w) (Carrier D w) a = x :=
  ⟨by intro h; exact (integers D w).exists_of_le_one h, by
    rintro ⟨a, rfl⟩
    exact (integers D w).map_le_one a⟩

theorem valuation_primitive :
    valuation D w (algebraMap (Ring D w) (Carrier D w) (primitive D w)) =
      WithZero.exp (-1 : ℤ) := by
  change (IsDiscreteValuationRing.maximalIdeal (Ring D w)).valuation (Carrier D w) _ = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact (IsDiscreteValuationRing.maximalIdeal (Ring D w)).intValuation_singleton
    (InitialThetaDeRhamDVR.primitive_ne_zero D w) (maximalIdeal_eq_span D w)

theorem valuation_lt_one_iff_theta_eq_zero (a : Ring D w) :
    valuation D w (algebraMap (Ring D w) (Carrier D w) a) < 1 ↔ theta D w a = 0 := by
  change (IsDiscreteValuationRing.maximalIdeal (Ring D w)).valuation (Carrier D w) _ < 1 ↔ _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  change a ∈ IsLocalRing.maximalIdeal (Ring D w) ↔ _
  rw [maximalIdeal_eq_kernel, RingHom.mem_ker]

theorem valuation_eq_one_iff_theta_ne_zero (a : Ring D w) :
    valuation D w (algebraMap (Ring D w) (Carrier D w) a) = 1 ↔ theta D w a ≠ 0 :=
  (integers D w).isUnit_iff_valuation_eq_one.symm.trans (isUnit_iff D w a)

theorem mem_kernel_pow_iff (n : ℕ) (a : Ring D w) :
    a ∈ RingHom.ker (theta D w) ^ n ↔
      valuation D w (algebraMap (Ring D w) (Carrier D w) a) ≤
        WithZero.exp (-1 : ℤ) ^ n := by
  rw [kernel_eq_span, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (integers D w).dvd_iff_le, map_pow, map_pow, valuation_primitive]

def integerEquiv : Ring D w ≃+* (valuation D w).integer :=
  RingEquiv.ofBijective
    ({
      toFun := fun a => ⟨algebraMap (Ring D w) (Carrier D w) a, (integers D w).map_le_one a⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b) } :
      Ring D w →+* (valuation D w).integer)
    ⟨fun a b h => (integers D w).hom_inj (congrArg Subtype.val h), fun x => by
      obtain ⟨a, ha⟩ := (integers D w).exists_of_le_one x.property
      exact ⟨a, Subtype.ext ha⟩⟩

theorem integerEquiv_coe (a : Ring D w) :
    (integerEquiv D w a : Carrier D w) = algebraMap (Ring D w) (Carrier D w) a := rfl

def integerTheta : (valuation D w).integer →+*
    InitialThetaCanonicalGeometricFontaine.coefficientField D w :=
  (theta D w).comp (integerEquiv D w).symm.toRingHom

theorem integerTheta_integerEquiv (a : Ring D w) :
    integerTheta D w (integerEquiv D w a) = theta D w a := by
  exact congrArg (theta D w) ((integerEquiv D w).symm_apply_apply a)

theorem integerTheta_surjective : Function.Surjective (integerTheta D w) :=
  (theta_surjective D w).comp (integerEquiv D w).symm.surjective

theorem integerTheta_eq_zero_iff (x : (valuation D w).integer) :
    integerTheta D w x = 0 ↔ valuation D w (x : Carrier D w) < 1 := by
  have hx : (integerEquiv D w ((integerEquiv D w).symm x) : Carrier D w) = x :=
    congrArg Subtype.val ((integerEquiv D w).apply_symm_apply x)
  rw [integerEquiv_coe] at hx
  rw [← hx]
  exact (valuation_lt_one_iff_theta_eq_zero D w ((integerEquiv D w).symm x)).symm

def integerQuotientEquiv :
    ((valuation D w).integer ⧸ RingHom.ker (integerTheta D w)) ≃+*
      InitialThetaCanonicalGeometricFontaine.coefficientField D w :=
  (integerTheta D w).quotientKerEquivOfSurjective (integerTheta_surjective D w)

theorem integerQuotientEquiv_mk (x : (valuation D w).integer) :
    integerQuotientEquiv D w (Ideal.Quotient.mk _ x) = integerTheta D w x :=
  RingHom.quotientKerEquivOfSurjective_apply_mk
    (f := integerTheta D w) (integerTheta_surjective D w) x

theorem nonzero_zpow_factorization (x : Carrier D w) (hx : x ≠ 0) :
    ∃ n : ℤ, ∃ u : (Ring D w)ˣ,
      x = u • algebraMap (Ring D w) (Carrier D w) (primitive D w) ^ n :=
  IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (InitialThetaDeRhamDVR.primitive_irreducible D w) hx

end
end JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation
