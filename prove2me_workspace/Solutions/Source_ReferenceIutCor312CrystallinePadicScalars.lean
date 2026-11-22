import Solutions.Source_ReferenceIutCor312CrystallineInvertP
import Mathlib.NumberTheory.Padics.RingHoms

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

variable (p : ℕ) [Fact p.Prime]

private theorem padicInt_addMonoidHom_ext_of_prime_pow_zero {R : Type*} [CommRing R]
    (k : ℕ) (hk : (p : R) ^ k = 0) (f g : PadicInt p →+ R)
    (hfg : f 1 = g 1) : f = g := by
  apply AddMonoidHom.ext
  intro a
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec k a)
  have hsub : a - (a.appr k : PadicInt p) = p ^ k • b := by
    rw [nsmul_eq_mul, Nat.cast_pow]
    exact hb
  have h (e : PadicInt p →+ R) : e a = a.appr k • e 1 := by
    have he := congrArg e hsub
    rw [map_sub, map_nsmul] at he
    rw [nsmul_eq_mul, Nat.cast_pow, hk, zero_mul] at he
    refine (sub_eq_zero.mp he).trans ?_
    simpa only [nsmul_eq_mul, mul_one] using map_nsmul e (a.appr k) (1 : PadicInt p)
  rw [h f, h g, hfg]

/-- An additive map from the p-adic integers to a p-adic completion is
determined by the image of one. -/
theorem padicInt_addMonoidHom_ext_to_completion {R : Type*} [CommRing R]
    (f g : PadicInt p →+ AdicCompletion (Ideal.span {(p : R)}) R)
    (hfg : f 1 = g 1) : f = g := by
  apply AddMonoidHom.ext
  intro a
  let J : Ideal R := Ideal.span {(p : R)}
  refine AdicCompletion.ext_evalₐ (I := J) ?_
  intro k
  let q := Ideal.Quotient.mk (J ^ k)
  have hzero : (p : R ⧸ J ^ k) ^ k = 0 := by
    rw [← map_natCast q p, ← map_pow q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (p : R)) k)
  let e := (AdicCompletion.evalₐ J k).toRingHom.toAddMonoidHom
  have he : (e.comp f) 1 = (e.comp g) 1 := congrArg e hfg
  exact DFunLike.congr_fun (padicInt_addMonoidHom_ext_of_prime_pow_zero p k hzero
    (e.comp f) (e.comp g) he) a

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

/-- Prime-field Witt vectors induce the integral p-adic scalars on the
crystalline completion. -/
def padicIntMapACris : PadicInt p →+* ACris C p :=
  (algebraMap (A0 C p) (ACris C p)).comp
    ((algebraMap (Ainf C p) (A0 C p)).comp
      ((WittVector.map (ZMod.castHom (dvd_refl p) (GeometricTiltField.Source C p))).comp
        (WittVector.equiv p).symm.toRingHom))

theorem mapACris_padicIntMapACris (f : ACris C p →+* ACris C p) (a : PadicInt p) :
    f (padicIntMapACris p C a) = padicIntMapACris p C a := by
  let j := padicIntMapACris p C
  have h1 : (f.comp j).toAddMonoidHom 1 = j.toAddMonoidHom 1 := by
    change f (j 1) = j 1
    rw [map_one j, map_one f]
  exact DFunLike.congr_fun (padicInt_addMonoidHom_ext_to_completion p
    (f.comp j).toAddMonoidHom j.toAddMonoidHom h1) a

def padicIntMapACrisInvertP : PadicInt p →+* ACrisInvertP C p :=
  (algebraMap (ACris C p) (ACrisInvertP C p)).comp (padicIntMapACris p C)

private theorem padicIntMapACrisInvertP_isUnit (a : PadicInt p) (ha : a ≠ 0) :
    IsUnit (padicIntMapACrisInvertP p C a) := by
  let f := padicIntMapACrisInvertP p C
  change IsUnit (f a)
  rw [PadicInt.unitCoeff_spec ha, map_mul f, map_pow f, map_natCast f]
  exact ((PadicInt.unitCoeff ha).isUnit.map f).mul
    ((ACrisInvertP_prime_isUnit C p).pow a.valuation)

/-- Rational p-adic scalars on the crystalline ring after inverting the prime. -/
def padicMapACrisInvertP : Padic p →+* ACrisInvertP C p :=
  IsLocalization.lift (M := nonZeroDivisors (PadicInt p))
    (S := Padic p) (g := padicIntMapACrisInvertP p C) fun y =>
      padicIntMapACrisInvertP_isUnit p C y.val (mem_nonZeroDivisors_iff_ne_zero.mp y.property)

instance instAlgebraPadicACrisInvertP : Algebra (Padic p) (ACrisInvertP C p) :=
  (padicMapACrisInvertP p C).toAlgebra

@[simp]
theorem padicMapACrisInvertP_algebraMap (a : PadicInt p) :
    padicMapACrisInvertP p C (algebraMap (PadicInt p) (Padic p) a) =
      padicIntMapACrisInvertP p C a :=
  IsLocalization.lift_eq _ a

theorem mapACrisInvertP_padicMapACrisInvertP (f : ACris C p →+* ACris C p) (a : Padic p) :
    mapACrisInvertP C p f (padicMapACrisInvertP p C a) = padicMapACrisInvertP p C a := by
  have h : (mapACrisInvertP C p f).comp (padicMapACrisInvertP p C) =
      padicMapACrisInvertP p C := by
    apply IsLocalization.ringHom_ext (M := nonZeroDivisors (PadicInt p))
    apply RingHom.ext
    intro b
    change mapACrisInvertP C p f (padicMapACrisInvertP p C (algebraMap _ _ b)) =
      padicMapACrisInvertP p C (algebraMap _ _ b)
    rw [padicMapACrisInvertP_algebraMap]
    change mapACrisInvertP C p f
        (algebraMap (ACris C p) (ACrisInvertP C p) (padicIntMapACris p C b)) =
      algebraMap (ACris C p) (ACrisInvertP C p) (padicIntMapACris p C b)
    rw [mapACrisInvertP_algebraMap, mapACris_padicIntMapACris]
  exact RingHom.congr_fun h a

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
