import ArithmeticTeichmullerSpaces.Act1Scene1.NormedIntegerLocalization
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFontaineKernel
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Perfectoid.BDeRham

/-!
source-id: JT-SCENE1-INITIAL-THETA-FONTAINE-LOCALIZATION
source: Joshi II eta_K, its principal kernel (838, 932), and the period-ring
evaluation leading to B_dR (1069--1076); Mathlib fontaineThetaInvertP.
fidelity: extends the same actual theta to W(O_F)[1/p], with exact kernel,
surjectivity and quotient equal to the original untilt field. Identifies
the source and target localizations with Mathlib's original Fontaine map.
No field/localization/kernel certificate is input. No Frechet norm or
Fargues--Fontaine analytic point is asserted. Original proofs; R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaFontaineLocalization

open JoshiTeich.Prologue InitialThetaTiltFontaine
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

/-- The existing actual untilt is the p-localization of its actual valuation integers. -/
instance untiltIsLocalization : IsLocalization.Away
    (Arithmetic.residueChar w.1 : LocalGeometricFontaine.integerRing
      (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w) := by
  apply NormedIntegerLocalization.field_isLocalization
  · exact Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero
  · exact (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out.2

local instance mappedUntiltIsLocalization : IsLocalization
    ((Submonoid.powers (Arithmetic.residueChar w.1 : Ainf D w)).map
      (InitialThetaTiltFontaine.theta D w))
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w) := by
  simpa only [Submonoid.map_powers, map_natCast] using untiltIsLocalization D w

abbrev AinfInvertP := Localization.Away (Arithmetic.residueChar w.1 : Ainf D w)

def theta : AinfInvertP D w →+* InitialThetaCanonicalGeometricFontaine.coefficientField D w :=
  IsLocalization.map _ (InitialThetaTiltFontaine.theta D w)
    (Submonoid.powers (Arithmetic.residueChar w.1 : Ainf D w)).le_comap_map

theorem theta_algebraMap (a : Ainf D w) :
    theta D w (algebraMap (Ainf D w) (AinfInvertP D w) a) =
      (InitialThetaTiltFontaine.theta D w a :
        InitialThetaCanonicalGeometricFontaine.coefficientField D w) := by
  simp only [theta, IsLocalization.map_eq]
  exact Algebra.algebraMap_ofSubsemiring_apply _ _

theorem theta_surjective : Function.Surjective (theta D w) :=
  IsLocalization.map_surjective_of_surjective
    (M := Submonoid.powers (Arithmetic.residueChar w.1 : Ainf D w))
    (S := AinfInvertP D w) (Q := InitialThetaCanonicalGeometricFontaine.coefficientField D w)
    (g := InitialThetaTiltFontaine.theta D w) (InitialThetaTiltFontaine.theta_surjective D w)

def localizedPrimitive : AinfInvertP D w :=
  algebraMap (Ainf D w) (AinfInvertP D w) (primitive D w)

theorem theta_localizedPrimitive : theta D w (localizedPrimitive D w) = 0 := by
  rw [localizedPrimitive, theta_algebraMap]
  exact congrArg Subtype.val (show InitialThetaTiltFontaine.theta D w (primitive D w) = 0 from
    primitive_mem_kernel D w)

theorem kernel_eq_span : RingHom.ker (theta D w) = Ideal.span {localizedPrimitive D w} := by
  calc
    RingHom.ker (theta D w) = (RingHom.ker (InitialThetaTiltFontaine.theta D w)).map
        (algebraMap (Ainf D w) (AinfInvertP D w)) :=
      IsLocalization.ker_map
        (Q := InitialThetaCanonicalGeometricFontaine.coefficientField D w)
        (S := AinfInvertP D w) (InitialThetaTiltFontaine.theta D w) rfl
    _ = _ := by
      simp only [InitialThetaFontaineKernel.kernel_eq_span, Ideal.map_span, Set.image_singleton,
        localizedPrimitive]

theorem mem_kernel_iff_dvd (a : AinfInvertP D w) :
    theta D w a = 0 ↔ localizedPrimitive D w ∣ a := by
  change a ∈ RingHom.ker (theta D w) ↔ _
  rw [kernel_eq_span, Ideal.mem_span_singleton]

theorem kernel_isMaximal : (RingHom.ker (theta D w)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (theta D w) (theta_surjective D w)

theorem prime_ne_zero : (Arithmetic.residueChar w.1 : Ainf D w) ≠ 0 := by
  intro h
  have hh := congrArg (InitialThetaTiltFontaine.theta D w) h
  rw [map_natCast, map_zero] at hh
  exact (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero) hh

theorem algebraMap_injective : Function.Injective (algebraMap (Ainf D w) (AinfInvertP D w)) := by
  apply IsLocalization.injective (M := Submonoid.powers (Arithmetic.residueChar w.1 : Ainf D w))
  rintro x ⟨n, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n (prime_ne_zero D w))

theorem localizedPrimitive_ne_zero : localizedPrimitive D w ≠ 0 := by
  intro h
  exact primitive_ne_zero D w
    (algebraMap_injective D w (h.trans (map_zero _).symm))

def quotientEquiv : (AinfInvertP D w ⧸ RingHom.ker (theta D w)) ≃+*
    InitialThetaCanonicalGeometricFontaine.coefficientField D w :=
  (theta D w).quotientKerEquivOfSurjective (theta_surjective D w)

def quotientPrimitiveEquiv : (AinfInvertP D w ⧸ Ideal.span {localizedPrimitive D w}) ≃+*
    InitialThetaCanonicalGeometricFontaine.coefficientField D w :=
  (Ideal.quotEquivOfEq (kernel_eq_span D w).symm).trans (quotientEquiv D w)

set_option maxHeartbeats 2000000 in
theorem quotientPrimitiveEquiv_mk (a : AinfInvertP D w) :
    quotientPrimitiveEquiv D w (Ideal.Quotient.mk _ a) = theta D w a := by
  unfold quotientPrimitiveEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk
    (f := theta D w) (theta_surjective D w) a

/-- Transport of the original PreTilt Witt localization, retaining the original p. -/
def sourceLocalizationEquiv :
    Localization.Away (Arithmetic.residueChar w.1 :
      WittVector (Arithmetic.residueChar w.1) (InitialThetaTiltField.Source D w)) ≃+* AinfInvertP D w :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (Arithmetic.residueChar w.1 :
      WittVector (Arithmetic.residueChar w.1) (InitialThetaTiltField.Source D w)))
    (T := Submonoid.powers (Arithmetic.residueChar w.1 : Ainf D w))
    _ _ (preTiltWittEquiv D w) (by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers
      (map_natCast (preTiltWittEquiv D w).toRingHom (Arithmetic.residueChar w.1)))

theorem sourceLocalizationEquiv_algebraMap
    (a : WittVector (Arithmetic.residueChar w.1) (InitialThetaTiltField.Source D w)) :
    sourceLocalizationEquiv D w (algebraMap _ _ a) =
      algebraMap (Ainf D w) (AinfInvertP D w) (preTiltWittEquiv D w a) := by
  simp only [sourceLocalizationEquiv, IsLocalization.ringEquivOfRingEquiv_eq]

def untiltLocalizationEquiv :
    Localization.Away (Arithmetic.residueChar w.1 : LocalGeometricFontaine.integerRing
      (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) ≃+*
      InitialThetaCanonicalGeometricFontaine.coefficientField D w :=
  (IsLocalization.algEquiv (Submonoid.powers (Arithmetic.residueChar w.1 :
    LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w)))
      _ _).toRingEquiv

theorem untiltLocalizationEquiv_algebraMap
    (a : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) :
    untiltLocalizationEquiv D w (algebraMap _ _ a) =
      (a : InitialThetaCanonicalGeometricFontaine.coefficientField D w) := by
  exact (IsLocalization.algEquiv (Submonoid.powers (Arithmetic.residueChar w.1 :
    LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w)))
      _ _).commutes a

/-- The localization diagram commutes with Mathlib's original fontaineThetaInvertP. -/
theorem theta_sourceLocalization
    (x : Localization.Away (Arithmetic.residueChar w.1 :
      WittVector (Arithmetic.residueChar w.1) (InitialThetaTiltField.Source D w))) :
    theta D w (sourceLocalizationEquiv D w x) =
      untiltLocalizationEquiv D w
        (fontaineThetaInvertP
          (LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
          (Arithmetic.residueChar w.1) x) := by
  have h : (theta D w).comp (sourceLocalizationEquiv D w).toRingHom =
      (untiltLocalizationEquiv D w).toRingHom.comp
        (fontaineThetaInvertP
          (LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
          (Arithmetic.residueChar w.1)) := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (Arithmetic.residueChar w.1 :
        WittVector (Arithmetic.residueChar w.1) (InitialThetaTiltField.Source D w)))
    ext a
    change theta D w (sourceLocalizationEquiv D w (algebraMap _ _ a)) = _
    rw [sourceLocalizationEquiv_algebraMap, theta_algebraMap,
      InitialThetaTiltFontaine.theta_preTiltWittEquiv]
    simp only [RingHom.comp_apply, fontaineThetaInvertP, Localization.awayLift,
      IsLocalization.Away.lift_eq]
    change (((InitialThetaCanonicalGeometricFontaine.placeData D w).data.theta a) :
      InitialThetaCanonicalGeometricFontaine.coefficientField D w) =
        untiltLocalizationEquiv D w (algebraMap _ _ (WittVector.fontaineTheta _ _ a))
    rw [untiltLocalizationEquiv_algebraMap]
    rfl
  exact congrArg (fun f => f x) h

end
end JoshiTeich.Act1Scene1.InitialThetaFontaineLocalization
