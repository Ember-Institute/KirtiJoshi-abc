import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTateFrobenius

/-!
source-id: JT-SCENE1-INITIAL-THETA-BOUNDED-WITT-LOCALIZATION
source: Joshi II se:ff-rings and pr:primitive-elements1, the inclusion
W(O_F) into B (511--512, 719--727), and the Frobenius-stable B+ (1051--1076).
fidelity: constructs the algebraic localization Ainf[1/p,1/[varpi]] from
the original contracting varpi with sharp(varpi)=p. Extends the original
Witt Frobenius and its inverse, and embeds this ring in the original
B_dR+ with the original theta evaluation. No rho norm or Frechet
completion, nor identification with the paper's completed B, is asserted.
Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaBoundedWittLocalization

open JoshiTeich.Prologue InitialThetaCanonicalGeometricFontaine
open InitialThetaTiltFontaine
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance primeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ < 1) := primeNormFact D w

def varpi : InitialThetaTiltIntegers.Integers D w := integralLift D w (Arithmetic.residueChar w.1)

theorem varpi_norm_pos_lt_one : 0 < ‖varpi D w‖ ∧ ‖varpi D w‖ < 1 := by
  have hn : ‖varpi D w‖ = ‖(Arithmetic.residueChar w.1 : coefficientField D w)‖ :=
    integralLift_norm D w _
  rw [hn]
  exact (primeNormFact D w).out

def teichVarpi : Ainf D w := WittVector.teichmuller (Arithmetic.residueChar w.1) (varpi D w)

theorem theta_teichVarpi : theta D w (teichVarpi D w) = Arithmetic.residueChar w.1 :=
  theta_integralLift D w _

def denominator : Ainf D w := (Arithmetic.residueChar w.1 : Ainf D w) * teichVarpi D w

theorem denominator_ne_zero : denominator D w ≠ 0 := by
  intro h
  have he := congrArg (theta D w) h
  rw [denominator, map_mul, map_natCast, theta_teichVarpi, map_zero] at he
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
    (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero) he

/-- Inverting the product inverts exactly the two specified elements. -/
abbrev Ring := Localization.Away (denominator D w)

def inclusion : Ainf D w →+* Ring D w := algebraMap _ _

theorem inclusion_injective : Function.Injective (inclusion D w) := by
  apply IsLocalization.injective (M := Submonoid.powers (denominator D w))
  rintro a ⟨n, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n (denominator_ne_zero D w))

instance domain : IsDomain (Ring D w) := Localization.Away.isDomain (denominator_ne_zero D w)

theorem prime_isUnit : IsUnit (inclusion D w (Arithmetic.residueChar w.1)) := by
  apply isUnit_of_mul_isUnit_left (y := inclusion D w (teichVarpi D w))
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (denominator D w)

theorem teichVarpi_isUnit : IsUnit (inclusion D w (teichVarpi D w)) := by
  apply isUnit_of_mul_isUnit_right (x := inclusion D w (Arithmetic.residueChar w.1))
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (denominator D w)

def sourceFrobenius : Ainf D w ≃+* Ainf D w :=
  WittVector.frobeniusEquiv (Arithmetic.residueChar w.1) (InitialThetaTiltIntegers.Integers D w)

theorem sourceFrobenius_teichVarpi :
    sourceFrobenius D w (teichVarpi D w) = teichVarpi D w ^ Arithmetic.residueChar w.1 := by
  change InitialThetaTateFrobenius.phi D w _ = _
  rw [teichVarpi, InitialThetaTateFrobenius.phi_teichmuller, map_pow]

theorem inverseFrobenius_teichVarpi_pow :
    ((sourceFrobenius D w).symm (teichVarpi D w)) ^ Arithmetic.residueChar w.1 = teichVarpi D w := by
  apply (sourceFrobenius D w).injective
  rw [map_pow, RingEquiv.apply_symm_apply, sourceFrobenius_teichVarpi]

theorem frobenius_denominator_isUnit : IsUnit
    ((inclusion D w).comp (sourceFrobenius D w).toRingHom (denominator D w)) := by
  change IsUnit (inclusion D w (sourceFrobenius D w
    ((Arithmetic.residueChar w.1 : Ainf D w) * teichVarpi D w)))
  rw [map_mul, map_natCast, sourceFrobenius_teichVarpi, map_mul, map_pow]
  exact (prime_isUnit D w).mul ((teichVarpi_isUnit D w).pow _)

theorem inverseFrobenius_denominator_isUnit : IsUnit
    ((inclusion D w).comp (sourceFrobenius D w).symm.toRingHom (denominator D w)) := by
  have hr : IsUnit (inclusion D w ((sourceFrobenius D w).symm (teichVarpi D w))) := by
    apply isUnit_of_dvd_unit (dvd_pow_self _ (Arithmetic.residueChar_prime w.1).ne_zero)
    rw [← map_pow, inverseFrobenius_teichVarpi_pow]
    exact teichVarpi_isUnit D w
  change IsUnit (inclusion D w ((sourceFrobenius D w).symm
    ((Arithmetic.residueChar w.1 : Ainf D w) * teichVarpi D w)))
  rw [map_mul, map_natCast, map_mul]
  exact (prime_isUnit D w).mul hr

def frobenius : Ring D w →+* Ring D w :=
  IsLocalization.Away.lift (denominator D w) (frobenius_denominator_isUnit D w)

def inverseFrobenius : Ring D w →+* Ring D w :=
  IsLocalization.Away.lift (denominator D w) (inverseFrobenius_denominator_isUnit D w)

theorem frobenius_inclusion (a : Ainf D w) :
    frobenius D w (inclusion D w a) = inclusion D w (sourceFrobenius D w a) :=
  IsLocalization.Away.lift_eq _ _ a

theorem inverseFrobenius_inclusion (a : Ainf D w) :
    inverseFrobenius D w (inclusion D w a) = inclusion D w ((sourceFrobenius D w).symm a) :=
  IsLocalization.Away.lift_eq _ _ a

def frobeniusEquiv : Ring D w ≃+* Ring D w where
  __ := frobenius D w
  invFun := inverseFrobenius D w
  left_inv x := by
    have he : (inverseFrobenius D w).comp (frobenius D w) = RingHom.id (Ring D w) := by
      apply IsLocalization.ringHom_ext (M := Submonoid.powers (denominator D w))
      ext a
      change inverseFrobenius D w (frobenius D w (inclusion D w a)) = inclusion D w a
      rw [frobenius_inclusion, inverseFrobenius_inclusion, RingEquiv.symm_apply_apply]
    exact RingHom.congr_fun he x
  right_inv x := by
    have he : (frobenius D w).comp (inverseFrobenius D w) = RingHom.id (Ring D w) := by
      apply IsLocalization.ringHom_ext (M := Submonoid.powers (denominator D w))
      ext a
      change frobenius D w (inverseFrobenius D w (inclusion D w a)) = inclusion D w a
      rw [inverseFrobenius_inclusion, frobenius_inclusion, RingEquiv.apply_symm_apply]
    exact RingHom.congr_fun he x

theorem denominator_image_isUnit : IsUnit
    (InitialThetaDeRhamTeichmuller.ainfToPlus D w (denominator D w)) := by
  apply (InitialThetaDeRhamCompletion.isUnit_iff D w _).mpr
  rw [InitialThetaDeRhamTeichmuller.theta_ainfToPlus, denominator, map_mul, map_natCast,
    theta_teichVarpi]
  change (Arithmetic.residueChar w.1 : coefficientField D w) * Arithmetic.residueChar w.1 ≠ 0
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
    (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)

def toDeRhamPlus : Ring D w →+* InitialThetaDeRhamCompletion.Ring D w :=
  IsLocalization.Away.lift (denominator D w) (denominator_image_isUnit D w)

theorem toDeRhamPlus_inclusion (a : Ainf D w) :
    toDeRhamPlus D w (inclusion D w a) = InitialThetaDeRhamTeichmuller.ainfToPlus D w a :=
  IsLocalization.Away.lift_eq _ _ a

theorem toDeRhamPlus_injective : Function.Injective (toDeRhamPlus D w) := by
  apply (injective_iff_map_eq_zero (toDeRhamPlus D w)).mpr
  intro x hx
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (denominator D w) x
  have hz : InitialThetaDeRhamTeichmuller.ainfToPlus D w a = 0 := by
    rw [← toDeRhamPlus_inclusion]
    change toDeRhamPlus D w (algebraMap (Ainf D w) (Ring D w) a) = 0
    rw [← ha, map_mul, hx, zero_mul]
  have ha0 : a = 0 := InitialThetaDeRhamEmbedding.ainfToPlus_injective D w
    (hz.trans (map_zero _).symm)
  rw [ha0, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (denominator D w) (S := Ring D w)).pow n).mul_left_eq_zero.mp ha

def evaluation : Ring D w →+* coefficientField D w :=
  (InitialThetaDeRhamCompletion.theta D w).comp (toDeRhamPlus D w)

theorem evaluation_inclusion (a : Ainf D w) :
    evaluation D w (inclusion D w a) = (theta D w a : coefficientField D w) := by
  rw [evaluation, RingHom.comp_apply, toDeRhamPlus_inclusion,
    InitialThetaDeRhamTeichmuller.theta_ainfToPlus]

/-- The original Tate coordinate now lives in a ring with the actual Frobenius automorphism. -/
def tateCoordinate (x : InitialThetaCyclotomicTateTilt.Tate D w) : Ring D w :=
  inclusion D w (InitialThetaCyclotomicTateTilt.kernelCoordinate D w x)

theorem frobenius_tateCoordinate (x : InitialThetaCyclotomicTateTilt.Tate D w) :
    frobeniusEquiv D w (tateCoordinate D w x) =
      tateCoordinate D w (x ^ Arithmetic.residueChar w.1) := by
  change frobenius D w (inclusion D w _) = _
  rw [frobenius_inclusion]
  exact congrArg (inclusion D w) (InitialThetaTateFrobenius.phi_kernelCoordinate D w x)

theorem toDeRhamPlus_tateCoordinate (x : InitialThetaCyclotomicTateTilt.Tate D w) :
    toDeRhamPlus D w (tateCoordinate D w x) = InitialThetaDeRhamLogarithm.tateCoordinate D w x :=
  toDeRhamPlus_inclusion D w _

theorem tateCoordinate_eq_zero_iff (x : InitialThetaCyclotomicTateTilt.Tate D w) :
    tateCoordinate D w x = 0 ↔ x = 1 := by
  change inclusion D w (InitialThetaCyclotomicTateTilt.kernelCoordinate D w x) = 0 ↔ _
  rw [← map_zero (inclusion D w), (inclusion_injective D w).eq_iff,
    InitialThetaCyclotomicTateTilt.kernelCoordinate_eq_zero_iff]

end
end JoshiTeich.Act1Scene1.InitialThetaBoundedWittLocalization
