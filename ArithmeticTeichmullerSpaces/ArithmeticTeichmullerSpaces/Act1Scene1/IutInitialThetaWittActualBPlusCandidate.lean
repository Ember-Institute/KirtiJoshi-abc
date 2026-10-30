import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoOneUnitBall
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusExpansion

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ACTUAL-BPLUS-CANDIDATE
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, where
the paper's B+ is the rho=1 unit ball in B (1051--1076, citing
Fargues--Fontaine Proposition 1.10.7).
fidelity: packages the proved rho=1 unit ball of the original bounded
Witt localization as an explicit actual subring and embeds it injectively
into the original common completion. Its membership is equivalent to the
constructed p-integral Ainf presentation. This is an actual candidate
carrier for later comparison; it is not renamed as the paper's B+ and
does not assume a Galois or holomorphoid marking. Original proofs; no
reference implementation copied.
boundary: Scene1/Derived; the full paper Frechet B, its Galois/Frobenius
actions and global holomorphoid identity remain open. Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittActualBPlusCandidate

open JoshiTeich.Prologue
open InitialThetaBoundedWittLocalization InitialThetaWittRhoNorm
open InitialThetaWittRhoOneUnitBall
open InitialThetaWittRhoFrobenius
open InitialThetaWittAllRadiusFrobenius
open InitialThetaBoundedWittPadicScalars
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def unitBallSubring : Subring (Ring D w) where
  carrier := {x | realValue D w 1 x ≤ 1}
  zero_mem' := by simp [realValue_zero]
  one_mem' := by simp [realValue_one]
  add_mem' := by
    intro x y hx hy
    change realValue D w 1 x ≤ 1 at hx
    change realValue D w 1 y ≤ 1 at hy
    exact (realValue_add_le_max D w 1 (by norm_num) (by norm_num) x y).trans
      (max_le hx hy)
  neg_mem' := by
    intro x hx
    change realValue D w 1 x ≤ 1 at hx
    change realValue D w 1 (-x) ≤ 1
    rw [realValue_neg D w 1 (by norm_num) (by norm_num)]
    simpa only [one_pow] using hx
  mul_mem' := by
    intro x y hx hy
    change realValue D w 1 x ≤ 1 at hx
    change realValue D w 1 y ≤ 1 at hy
    exact (realValue_mul_le D w 1 (by norm_num) (by norm_num) x y).trans
      (by simpa using mul_le_mul hx hy (realValue_nonneg D w 1 y) (by norm_num))

theorem mem_unitBallSubring_iff (x : Ring D w) :
    x ∈ unitBallSubring D w ↔ realValue D w 1 x ≤ 1 := Iff.rfl

theorem mem_unitBallSubring_iff_pIntegral (x : Ring D w) :
    x ∈ unitBallSubring D w ↔ HasPIntegralPresentation D w x :=
  (mem_unitBallSubring_iff D w x).trans
    (unitBallAtOne_iff_hasPIntegralPresentation D w x)

def unitBallToCommon : unitBallSubring D w →+*
    InitialThetaWittAllRadiusCompletion.Carrier D w :=
  (InitialThetaWittAllRadiusCompletion.inclusion D w).comp
    (unitBallSubring D w).subtype

theorem unitBallToCommon_injective : Function.Injective (unitBallToCommon D w) := by
  intro x y h
  apply Subtype.ext
  apply InitialThetaWittAllRadiusCompletion.inclusion_injective D w
  exact h

theorem unitBallToCommon_apply (x : unitBallSubring D w) :
    unitBallToCommon D w x =
      InitialThetaWittAllRadiusCompletion.inclusion D w x.1 := rfl

theorem frobenius_mem_unitBallSubring (x : unitBallSubring D w) :
    InitialThetaBoundedWittLocalization.frobeniusEquiv D w x.1 ∈
      unitBallSubring D w := by
  change realValue D w 1
      (InitialThetaBoundedWittLocalization.frobeniusEquiv D w x.1) ≤ 1
  have h := InitialThetaWittRhoFrobenius.realValue_frobenius D w 1
    (by norm_num) ENNReal.one_ne_top x.1
  simpa only [one_pow] using (h.trans_le
    (pow_le_one₀ (realValue_nonneg D w 1 x.1) x.property))

def unitBallFrobenius : unitBallSubring D w →+* unitBallSubring D w :=
  ((InitialThetaBoundedWittLocalization.frobeniusEquiv D w).toRingHom.comp
    (unitBallSubring D w).subtype).codRestrict _ (frobenius_mem_unitBallSubring D w)

theorem unitBallFrobenius_apply (x : unitBallSubring D w) :
    (unitBallFrobenius D w x : Ring D w) =
      InitialThetaBoundedWittLocalization.frobeniusEquiv D w x.1 := rfl

theorem inverseFrobenius_mem_unitBallSubring (x : unitBallSubring D w) :
    (InitialThetaBoundedWittLocalization.frobeniusEquiv D w).symm x.1 ∈
      unitBallSubring D w := by
  change realValue D w 1
      ((InitialThetaBoundedWittLocalization.frobeniusEquiv D w).symm x.1) ≤ 1
  have h := InitialThetaWittRhoFrobenius.realValue_frobenius D w 1
    (by norm_num) ENNReal.one_ne_top
    ((InitialThetaBoundedWittLocalization.frobeniusEquiv D w).symm x.1)
  have hx : realValue D w 1 x.1 ≤ 1 := x.property
  have hp : realValue D w 1
      ((InitialThetaBoundedWittLocalization.frobeniusEquiv D w).symm x.1) ^
        Arithmetic.residueChar w.1 ≤ 1 := by
    rw [← h, (InitialThetaBoundedWittLocalization.frobeniusEquiv D w).apply_symm_apply]
    simpa only [one_pow] using hx
  exact le_of_pow_le_pow_left₀ (Arithmetic.residueChar_prime w.1).ne_zero
    (by norm_num) (by simpa using hp)

def unitBallInverseFrobenius : unitBallSubring D w →+* unitBallSubring D w :=
  ((InitialThetaBoundedWittLocalization.frobeniusEquiv D w).symm.toRingHom.comp
    (unitBallSubring D w).subtype).codRestrict _
      (inverseFrobenius_mem_unitBallSubring D w)

theorem unitBallInverseFrobenius_apply (x : unitBallSubring D w) :
    (unitBallInverseFrobenius D w x : Ring D w) =
      (InitialThetaBoundedWittLocalization.frobeniusEquiv D w).symm x.1 := rfl

theorem unitBallFrobenius_leftInverse (x : unitBallSubring D w) :
    unitBallInverseFrobenius D w (unitBallFrobenius D w x) = x := by
  apply Subtype.ext
  simp [unitBallInverseFrobenius, unitBallFrobenius]

theorem unitBallFrobenius_rightInverse (x : unitBallSubring D w) :
    unitBallFrobenius D w (unitBallInverseFrobenius D w x) = x := by
  apply Subtype.ext
  simp [unitBallInverseFrobenius, unitBallFrobenius]

def unitBallFrobeniusEquiv : unitBallSubring D w ≃+* unitBallSubring D w :=
  RingEquiv.ofBijective (unitBallFrobenius D w) (by
    constructor
    · intro x y h
      apply_fun unitBallInverseFrobenius D w at h
      simpa only [unitBallFrobenius_leftInverse] using h
    · intro y
      exact ⟨unitBallInverseFrobenius D w y,
        unitBallFrobenius_rightInverse D w y⟩)

theorem unitBallFrobeniusEquiv_apply (x : unitBallSubring D w) :
    unitBallFrobeniusEquiv D w x = unitBallFrobenius D w x := by
  rfl

theorem unitBallToCommon_frobenius (x : unitBallSubring D w) :
    unitBallToCommon D w (unitBallFrobenius D w x) =
      InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
        (unitBallToCommon D w x) := by
  rw [unitBallToCommon_apply, unitBallFrobenius_apply, unitBallToCommon_apply,
    InitialThetaWittAllRadiusFrobenius.frobenius_inclusion]

theorem padicIntMap_mem_unitBallSubring
    (a : PadicInt (Arithmetic.residueChar w.1)) :
    padicIntMap D w a ∈ unitBallSubring D w := by
  apply (mem_unitBallSubring_iff_pIntegral D w _).mpr
  let b : InitialThetaTiltFontaine.Ainf D w :=
    WittVector.map
      (ZMod.castHom (dvd_refl (Arithmetic.residueChar w.1))
        (InitialThetaTiltIntegers.Integers D w))
      ((WittVector.equiv (Arithmetic.residueChar w.1)).symm a)
  refine ⟨0, b, ?_⟩
  change padicIntMap D w a * (Arithmetic.residueChar w.1 : Ring D w) ^ 0 =
    InitialThetaBoundedWittLocalization.inclusion D w b
  simp only [pow_zero, mul_one, padicIntMap, InitialThetaBoundedWittRationalScalars.primeWittMap,
    b, RingHom.comp_apply]
  rfl

def padicIntMap :
    PadicInt (Arithmetic.residueChar w.1) →+* unitBallSubring D w :=
  (InitialThetaBoundedWittPadicScalars.padicIntMap D w).codRestrict _
    (padicIntMap_mem_unitBallSubring D w)

instance unitBallPadicIntAlgebra :
    Algebra (PadicInt (Arithmetic.residueChar w.1)) (unitBallSubring D w) :=
  (padicIntMap D w).toAlgebra

theorem padicIntMap_apply (a : PadicInt (Arithmetic.residueChar w.1)) :
    (padicIntMap D w a : Ring D w) =
      InitialThetaBoundedWittPadicScalars.padicIntMap D w a := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaWittActualBPlusCandidate
