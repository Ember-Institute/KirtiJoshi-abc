import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittLocalization

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-LOCALIZATION-CHOICE
source: Joshi II se:ff-rings / W(O_F) into B (511--512, 719--727);
the actual norm valuation integers, Teichmuller multiplication and localization.
fidelity: proves every nonzero integral Teichmuller element is inverted
in the existing two-element localization. Constructs the algebra equivalence
for every other nonzero contracting element, fixing the original Ainf.
Gives its universal mapping property, de Rham compatibility and the actual
Witt Frobenius on the alternative carrier. No bounded-expansion or rho-norm
identity is assumed. Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittLocalizationChoice

open JoshiTeich.Prologue InitialThetaCanonicalGeometricFontaine InitialThetaTiltFontaine
open InitialThetaBoundedWittLocalization
noncomputable section
universe u v
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem dvd_contraction_pow (s a : InitialThetaTiltIntegers.Integers D w)
    (hs : ‖s‖ < 1) (ha : a ≠ 0) : ∃ n : ℕ, a ∣ s ^ n := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr ha) hs
  refine ⟨n, ?_⟩
  apply (Valuation.integer.integers
    (NormedField.valuation (K := InitialThetaTiltField.Carrier D w))).dvd_of_le
  have he : ‖s ^ n‖ ≤ ‖a‖ := by rw [norm_pow]; exact hn.le
  exact_mod_cast he

theorem teichmuller_isUnit_of_contraction {R : Type v} [CommRing R]
    (f : Ainf D w →+* R) (s : InitialThetaTiltIntegers.Integers D w)
    (hs : ‖s‖ < 1) (hunit : IsUnit (f (WittVector.teichmuller (Arithmetic.residueChar w.1) s)))
    (a : InitialThetaTiltIntegers.Integers D w) (ha : a ≠ 0) :
    IsUnit (f (WittVector.teichmuller (Arithmetic.residueChar w.1) a)) := by
  obtain ⟨n, hn⟩ := dvd_contraction_pow D w s a hs ha
  have hd := map_dvd f (map_dvd (WittVector.teichmuller (Arithmetic.residueChar w.1)) hn)
  rw [map_pow, map_pow] at hd
  exact isUnit_of_dvd_unit hd (hunit.pow n)

/-- The existing ring already inverts every nonzero integral Teichmuller element. -/
theorem teichmuller_isUnit (a : InitialThetaTiltIntegers.Integers D w) (ha : a ≠ 0) :
    IsUnit (inclusion D w (WittVector.teichmuller (Arithmetic.residueChar w.1) a)) :=
  teichmuller_isUnit_of_contraction D w (inclusion D w) (varpi D w)
    (varpi_norm_pos_lt_one D w).2 (teichVarpi_isUnit D w) a ha

def choiceDenominator (s : InitialThetaTiltIntegers.Integers D w) : Ainf D w :=
  (Arithmetic.residueChar w.1 : Ainf D w) * WittVector.teichmuller (Arithmetic.residueChar w.1) s

abbrev ChoiceRing (s : InitialThetaTiltIntegers.Integers D w) :=
  Localization.Away (choiceDenominator D w s)

theorem choice_prime_isUnit (s : InitialThetaTiltIntegers.Integers D w) :
    IsUnit (algebraMap (Ainf D w) (ChoiceRing D w s) (Arithmetic.residueChar w.1)) := by
  apply isUnit_of_mul_isUnit_left
    (y := algebraMap (Ainf D w) (ChoiceRing D w s)
      (WittVector.teichmuller (Arithmetic.residueChar w.1) s))
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (choiceDenominator D w s)

theorem choice_teich_isUnit (s : InitialThetaTiltIntegers.Integers D w) :
    IsUnit (algebraMap (Ainf D w) (ChoiceRing D w s)
      (WittVector.teichmuller (Arithmetic.residueChar w.1) s)) := by
  apply isUnit_of_mul_isUnit_right
    (x := algebraMap (Ainf D w) (ChoiceRing D w s) (Arithmetic.residueChar w.1))
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (choiceDenominator D w s)

def toCanonical (s : InitialThetaTiltIntegers.Integers D w) (hs : s ≠ 0) :
    ChoiceRing D w s →+* InitialThetaBoundedWittLocalization.Ring D w :=
  IsLocalization.Away.lift (choiceDenominator D w s) (g := inclusion D w) (by
    change IsUnit (inclusion D w ((Arithmetic.residueChar w.1 : Ainf D w) *
      WittVector.teichmuller (Arithmetic.residueChar w.1) s))
    rw [map_mul]
    exact (prime_isUnit D w).mul (teichmuller_isUnit D w s hs))

def fromCanonical (s : InitialThetaTiltIntegers.Integers D w) (hs : ‖s‖ < 1) :
    InitialThetaBoundedWittLocalization.Ring D w →+* ChoiceRing D w s :=
  IsLocalization.Away.lift (denominator D w)
    (g := algebraMap (Ainf D w) (ChoiceRing D w s)) (by
      change IsUnit (algebraMap (Ainf D w) (ChoiceRing D w s)
        ((Arithmetic.residueChar w.1 : Ainf D w) * teichVarpi D w))
      rw [map_mul]
      exact (choice_prime_isUnit D w s).mul
        (teichmuller_isUnit_of_contraction D w _ s hs (choice_teich_isUnit D w s)
          (varpi D w) (norm_pos_iff.mp (varpi_norm_pos_lt_one D w).1)))

theorem toCanonical_inclusion (s : InitialThetaTiltIntegers.Integers D w) (hs : s ≠ 0)
    (a : Ainf D w) : toCanonical D w s hs (algebraMap _ _ a) = inclusion D w a :=
  IsLocalization.Away.lift_eq _ _ a

theorem fromCanonical_inclusion (s : InitialThetaTiltIntegers.Integers D w) (hs : ‖s‖ < 1)
    (a : Ainf D w) : fromCanonical D w s hs (inclusion D w a) = algebraMap _ _ a :=
  IsLocalization.Away.lift_eq _ _ a

/-- The equivalence fixes the original Ainf and retains both localization maps. -/
def choiceEquiv (s : InitialThetaTiltIntegers.Integers D w) (hs0 : s ≠ 0) (hs1 : ‖s‖ < 1) :
    ChoiceRing D w s ≃ₐ[Ainf D w] InitialThetaBoundedWittLocalization.Ring D w where
  __ := toCanonical D w s hs0
  invFun := fromCanonical D w s hs1
  commutes' := toCanonical_inclusion D w s hs0
  left_inv x := by
    have he : (fromCanonical D w s hs1).comp (toCanonical D w s hs0) =
        RingHom.id (ChoiceRing D w s) := by
      apply IsLocalization.ringHom_ext (M := Submonoid.powers (choiceDenominator D w s))
      ext a
      change fromCanonical D w s hs1 (toCanonical D w s hs0 (algebraMap _ _ a)) = algebraMap _ _ a
      rw [toCanonical_inclusion, fromCanonical_inclusion]
    exact RingHom.congr_fun he x
  right_inv x := by
    have he : (toCanonical D w s hs0).comp (fromCanonical D w s hs1) =
        RingHom.id (InitialThetaBoundedWittLocalization.Ring D w) := by
      apply IsLocalization.ringHom_ext (M := Submonoid.powers (denominator D w))
      ext a
      change toCanonical D w s hs0 (fromCanonical D w s hs1 (inclusion D w a)) = inclusion D w a
      rw [fromCanonical_inclusion, toCanonical_inclusion]
    exact RingHom.congr_fun he x

def choiceToDeRhamPlus (s : InitialThetaTiltIntegers.Integers D w) (hs : s ≠ 0) :
    ChoiceRing D w s →+* InitialThetaDeRhamCompletion.Ring D w :=
  (toDeRhamPlus D w).comp (toCanonical D w s hs)

theorem choiceToDeRhamPlus_inclusion (s : InitialThetaTiltIntegers.Integers D w) (hs : s ≠ 0)
    (a : Ainf D w) : choiceToDeRhamPlus D w s hs (algebraMap _ _ a) =
      InitialThetaDeRhamTeichmuller.ainfToPlus D w a := by
  rw [choiceToDeRhamPlus, RingHom.comp_apply, toCanonical_inclusion, toDeRhamPlus_inclusion]

def choiceFrobenius (s : InitialThetaTiltIntegers.Integers D w) (hs0 : s ≠ 0) (hs1 : ‖s‖ < 1) :
    ChoiceRing D w s ≃+* ChoiceRing D w s :=
  (choiceEquiv D w s hs0 hs1).toRingEquiv.trans
    ((frobeniusEquiv D w).trans (choiceEquiv D w s hs0 hs1).symm.toRingEquiv)

theorem choiceFrobenius_inclusion (s : InitialThetaTiltIntegers.Integers D w)
    (hs0 : s ≠ 0) (hs1 : ‖s‖ < 1) (a : Ainf D w) :
    choiceFrobenius D w s hs0 hs1 (algebraMap _ _ a) =
      algebraMap (Ainf D w) (ChoiceRing D w s) (sourceFrobenius D w a) := by
  change (choiceEquiv D w s hs0 hs1).symm
    (frobenius D w (toCanonical D w s hs0 (algebraMap _ _ a))) = _
  rw [toCanonical_inclusion, frobenius_inclusion]
  exact (choiceEquiv D w s hs0 hs1).symm.commutes _

theorem choiceToDeRhamPlus_injective (s : InitialThetaTiltIntegers.Integers D w)
    (hs0 : s ≠ 0) (hs1 : ‖s‖ < 1) : Function.Injective (choiceToDeRhamPlus D w s hs0) :=
  (toDeRhamPlus_injective D w).comp (choiceEquiv D w s hs0 hs1).injective

/-- Universal factorization for maps inverting p and all nonzero integral Teichmuller elements. -/
def lift {R : Type v} [CommRing R] (f : Ainf D w →+* R)
    (hp : IsUnit (f (Arithmetic.residueChar w.1)))
    (hT : ∀ a : InitialThetaTiltIntegers.Integers D w, a ≠ 0 →
      IsUnit (f (WittVector.teichmuller (Arithmetic.residueChar w.1) a))) :
    InitialThetaBoundedWittLocalization.Ring D w →+* R :=
  IsLocalization.Away.lift (denominator D w) (g := f) (by
    change IsUnit (f ((Arithmetic.residueChar w.1 : Ainf D w) * teichVarpi D w))
    rw [map_mul]
    exact hp.mul (hT (varpi D w) (norm_pos_iff.mp (varpi_norm_pos_lt_one D w).1)))

theorem lift_inclusion {R : Type v} [CommRing R] (f : Ainf D w →+* R) (hp hT) (a : Ainf D w) :
    lift D w f hp hT (inclusion D w a) = f a := IsLocalization.Away.lift_eq _ _ a

theorem lift_unique {R : Type v} [CommRing R] (f : Ainf D w →+* R) (hp hT)
    (g : InitialThetaBoundedWittLocalization.Ring D w →+* R)
    (hg : ∀ a : Ainf D w, g (inclusion D w a) = f a) : g = lift D w f hp hT := by
  apply IsLocalization.ringHom_ext (M := Submonoid.powers (denominator D w))
  ext a
  exact (hg a).trans (lift_inclusion D w f hp hT a).symm

end
end JoshiTeich.Act1Scene1.InitialThetaWittLocalizationChoice
