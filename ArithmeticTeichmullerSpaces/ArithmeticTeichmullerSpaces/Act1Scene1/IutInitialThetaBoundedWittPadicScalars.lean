import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittRationalScalars

/-!
source-id: JT-SCENE1-INITIAL-THETA-BOUNDED-WITT-PADIC-SCALARS
source: Joshi II `se:ff-rings`, the Q_p algebra of bounded period elements;
Mathlib WittVector.Compare, DiscreteValuationRing and PadicInt.isFractionRing.
fidelity: every nonzero prime-field Witt constant becomes a unit in
the actual bounded localization. The Witt comparison map then embeds
Z_p and its fraction field Q_p into the same ring. Proves rational
compatibility and that the original Frobenius fixes all these scalars.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; continuity, scalar norm laws, Tate-log and
paper B/BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaBoundedWittPadicScalars

open JoshiTeich.Prologue
open InitialThetaBoundedWittLocalization InitialThetaBoundedWittRationalScalars
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem primeWittMap_isUnit
    (a : WittVector (Arithmetic.residueChar w.1) (ZMod (Arithmetic.residueChar w.1)))
    (ha : a ≠ 0) : IsUnit (primeWittMap D w a) := by
  obtain ⟨m, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' a ha
  rw [map_mul, map_pow, map_natCast]
  have hp : IsUnit (Arithmetic.residueChar w.1 : InitialThetaBoundedWittLocalization.Ring D w) := by
    simpa only [map_natCast] using prime_isUnit D w
  exact (hp.pow m).mul (u.isUnit.map (primeWittMap D w))

def padicIntMap : PadicInt (Arithmetic.residueChar w.1) →+* InitialThetaBoundedWittLocalization.Ring D w :=
  (primeWittMap D w).comp (WittVector.equiv (Arithmetic.residueChar w.1)).symm.toRingHom

theorem padicIntMap_isUnit (a : PadicInt (Arithmetic.residueChar w.1)) (ha : a ≠ 0) :
    IsUnit (padicIntMap D w a) := by
  apply primeWittMap_isUnit D w
  intro hz
  apply ha
  apply (WittVector.equiv (Arithmetic.residueChar w.1)).symm.injective
  exact hz.trans (map_zero _).symm

def padicMap : Padic (Arithmetic.residueChar w.1) →+* InitialThetaBoundedWittLocalization.Ring D w :=
  IsLocalization.lift (M := nonZeroDivisors (PadicInt (Arithmetic.residueChar w.1)))
    (S := Padic (Arithmetic.residueChar w.1)) (g := padicIntMap D w)
    (fun y => padicIntMap_isUnit D w y.val (mem_nonZeroDivisors_iff_ne_zero.mp y.property))

instance boundedPadicAlgebra :
    Algebra (Padic (Arithmetic.residueChar w.1)) (InitialThetaBoundedWittLocalization.Ring D w) :=
  (padicMap D w).toAlgebra

theorem padicMap_injective : Function.Injective (padicMap D w) := (padicMap D w).injective

theorem padicMap_algebraMap (a : PadicInt (Arithmetic.residueChar w.1)) :
    padicMap D w (algebraMap _ (Padic (Arithmetic.residueChar w.1)) a) = padicIntMap D w a :=
  IsLocalization.lift_eq _ a

theorem padicMap_rational (q : ℚ) :
    padicMap D w (algebraMap ℚ (Padic (Arithmetic.residueChar w.1)) q) = rationalMap D w q :=
  RingHom.map_rat_algebraMap (padicMap D w) q

theorem frobenius_primeWitt
    (a : WittVector (Arithmetic.residueChar w.1) (ZMod (Arithmetic.residueChar w.1))) :
    frobeniusEquiv D w (primeWittMap D w a) = primeWittMap D w a := by
  change frobenius D w (inclusion D w _) = inclusion D w _
  rw [frobenius_inclusion]
  apply congrArg (inclusion D w)
  apply WittVector.ext
  intro n
  change (WittVector.frobenius (WittVector.map _ a)).coeff n = (WittVector.map _ a).coeff n
  simp only [WittVector.coeff_frobenius_charP, WittVector.map_coeff, ← map_pow, ZMod.pow_card]

theorem frobenius_padicInt (a : PadicInt (Arithmetic.residueChar w.1)) :
    frobeniusEquiv D w (padicIntMap D w a) = padicIntMap D w a :=
  frobenius_primeWitt D w ((WittVector.equiv (Arithmetic.residueChar w.1)).symm a)

theorem frobenius_padic (a : Padic (Arithmetic.residueChar w.1)) :
    frobeniusEquiv D w (padicMap D w a) = padicMap D w a := by
  have he : (frobeniusEquiv D w).toRingHom.comp (padicMap D w) = padicMap D w := by
    apply IsLocalization.ringHom_ext (M := nonZeroDivisors (PadicInt (Arithmetic.residueChar w.1)))
    ext b
    change frobeniusEquiv D w (padicMap D w (algebraMap _ _ b)) =
      padicMap D w (algebraMap _ _ b)
    rw [padicMap_algebraMap, frobenius_padicInt]
  exact RingHom.congr_fun he a

end
end JoshiTeich.Act1Scene1.InitialThetaBoundedWittPadicScalars
