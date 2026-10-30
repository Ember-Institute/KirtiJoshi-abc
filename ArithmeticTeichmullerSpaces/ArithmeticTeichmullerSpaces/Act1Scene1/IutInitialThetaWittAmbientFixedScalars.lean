import ArithmeticTeichmullerSpaces.Act1Scene1.WittFractionFrobeniusFixed
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittPadicScalars
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoFrobenius

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-AMBIENT-FIXED-SCALARS
source: Joshi II `se:ff-rings` and `eq:tate-module-of-lubin-tate`,
Q_p scalars for comparison of actual twisted period solutions.
fidelity: the prime-field Witt numerator agrees with the project's
existing PadicInt map in the original ambient Witt fraction field.
The constructed fixed-fraction presentation then gives an actual Q_p
scalar through the existing padicMap. Conversely those scalars are
fixed by the original ambient Frobenius. No parallel scalar embedding
or numerator-presentation hypothesis is introduced. Original proofs;
no reference implementation copied.
boundary: Scene1/Derived; this classifies fixed elements of the actual
algebraic ambient fraction field. Completed twisted-solution comparison,
the full Tate kernel and paper B/BK identities remain separate. R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittAmbientFixedScalars

open JoshiTeich.Prologue InitialThetaBoundedWittExpansion
open InitialThetaBoundedWittPadicScalars InitialThetaWittRhoFrobenius
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem toAmbient_padicInt_equiv
    (b : WittVector (Arithmetic.residueChar w.1) (ZMod (Arithmetic.residueChar w.1))) :
    toAmbient D w (padicIntMap D w (WittVector.equiv (Arithmetic.residueChar w.1) b)) =
      algebraMap (FieldWitt D w) (Ambient D w)
        (WittVector.map (ZMod.castHom (dvd_refl (Arithmetic.residueChar w.1))
          (InitialThetaTiltField.Carrier D w)) b) := by
  change toAmbient D w (InitialThetaBoundedWittRationalScalars.primeWittMap D w
    ((WittVector.equiv (Arithmetic.residueChar w.1)).symm
      (WittVector.equiv (Arithmetic.residueChar w.1) b))) = _
  rw [RingEquiv.symm_apply_apply]
  change toAmbient D w (InitialThetaBoundedWittLocalization.inclusion D w _) = _
  rw [toAmbient_inclusion]
  apply congrArg (algebraMap (FieldWitt D w) (Ambient D w))
  apply WittVector.ext
  intro n
  change (WittVector.map _ (WittVector.map _ b)).coeff n = (WittVector.map _ b).coeff n
  simp only [WittVector.map_coeff]
  generalize b.coeff n = z
  rw [← ZMod.natCast_zmod_val z]
  simp only [map_natCast]

theorem ambientFrobenius_eq_self_iff (x : Ambient D w) :
    ambientFrobenius D w x = x ↔
      ∃ c : Padic (Arithmetic.residueChar w.1), toAmbient D w (padicMap D w c) = x := by
  constructor
  · intro hx
    obtain ⟨m, b, hb⟩ := WittFractionFrobeniusFixed.exists_fixed_prime_presentation
      (Arithmetic.residueChar w.1) x hx
    let a : PadicInt (Arithmetic.residueChar w.1) :=
      WittVector.equiv (Arithmetic.residueChar w.1) b
    let c : Padic (Arithmetic.residueChar w.1) :=
      algebraMap _ _ a / (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ m
    have hp : (Arithmetic.residueChar w.1 : Ambient D w) ≠ 0 :=
      WittVector.FractionRing.p_nonzero (Arithmetic.residueChar w.1)
        (InitialThetaTiltField.Carrier D w)
    have hpc : (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero
    refine ⟨c, ?_⟩
    apply mul_right_cancel₀ (pow_ne_zero m hp)
    calc
      _ = toAmbient D w (padicMap D w
          (c * (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ m)) := by
        rw [map_mul, map_mul, map_pow, map_natCast, map_pow, map_natCast]
      _ = toAmbient D w (padicIntMap D w a) := by
        rw [show c * (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ m =
          algebraMap _ _ a from div_mul_cancel₀ _ (pow_ne_zero m hpc), padicMap_algebraMap]
      _ = _ := (toAmbient_padicInt_equiv D w b).trans hb.symm
  · rintro ⟨c, rfl⟩
    rw [← toAmbient_frobenius, frobenius_padic]

end
end JoshiTeich.Act1Scene1.InitialThetaWittAmbientFixedScalars
