import ArithmeticTeichmullerSpaces.Act1Scene1.LocalizationFrobeniusNaturality
import ArithmeticTeichmullerSpaces.Act1Scene1.RingEquivDictionaryTransport

/-!
source-id: JT-SCENE1-LOCALIZATION-FROBENIUS-RECAST
source: Joshi II `se:ff-rings`, functorial Frobenius on bounded Witt
localizations; localization naturality and transport along operation equalities.
fidelity: recasts an original ring equivalence along four explicit dictionary
equalities, applies localization naturality, and returns the result to the
original forward function. The old dictionaries are ordinary implicit
parameters. The integral law and conclusion use explicit projections from
the original equivalence. No concrete dictionary equality is assumed by a
consumer without a proof. Original proof; no reference implementation copied.
boundary: generic implication only; no norm, actual source law, completion,
or paper identity is supplied. Original functions and carriers are retained.
-/

namespace JoshiTeich.Act1Scene1.LocalizationFrobeniusNaturality

/-- Select multiplication from the supplied commutative ring dictionary. -/
def commRingMul {R : Type*} (c : CommRing R) : Mul R :=
  @Distrib.toMul R
    (@instDistribOfSemiring R
      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R c)))

/-- Select addition from the supplied commutative ring dictionary. -/
def commRingAdd {R : Type*} (c : CommRing R) : Add R :=
  @Distrib.toAdd R
    (@instDistribOfSemiring R
      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R c)))

theorem commutes_equiv_recast
    {A B L T : Type*}
    [cA : CommRing A] [cB : CommRing B] [cL : CommRing L] [cT : CommRing T]
    [algAL : Algebra A L] (M : Submonoid A) [loc : IsLocalization M L]
    (i : A →+* L) (j : B →+* T)
    (hi : ∀ a, i a = algebraMap A L a)
    {oldMulL : Mul L} {oldMulT : Mul T}
    {oldAddL : Add L} {oldAddT : Add T}
    (E : @RingEquiv L T oldMulL oldMulT oldAddL oldAddT)
    (hmL : oldMulL = commRingMul cL)
    (hmT : oldMulT = commRingMul cT)
    (haL : oldAddL = commRingAdd cL)
    (haT : oldAddT = commRingAdd cT)
    (F : @RingEquiv L L (commRingMul cL) (commRingMul cL)
      (commRingAdd cL) (commRingAdd cL))
    (G : @RingEquiv T T (commRingMul cT) (commRingMul cT)
      (commRingAdd cT) (commRingAdd cT))
    (e : A → B) (f : A → A) (g : B → B)
    (hE : ∀ a,
      @Equiv.toFun L T
          (@RingEquiv.toEquiv L T oldMulL oldMulT oldAddL oldAddT E) (i a) =
        j (e a))
    (hF : ∀ a, F (i a) = i (f a))
    (hG : ∀ b, G (j b) = j (g b))
    (he : ∀ a, e (f a) = g (e a))
    (x : L) :
    @Equiv.toFun L T
        (@RingEquiv.toEquiv L T oldMulL oldMulT oldAddL oldAddT E) (F x) =
      G (@Equiv.toFun L T
        (@RingEquiv.toEquiv L T oldMulL oldMulT oldAddL oldAddT E) x) := by
  let E' : @RingEquiv L T (commRingMul cL) (commRingMul cT)
      (commRingAdd cL) (commRingAdd cT) :=
    RingEquivDictionaryTransport.recast E hmL hmT haL haT
  have hfun := RingEquivDictionaryTransport.recast_toFun E hmL hmT haL haT
  have hE' : ∀ a, E' (i a) = j (e a) := by
    intro a
    exact (congrFun hfun (i a)).trans (hE a)
  have hcomm := @commutes_equiv A B L T cA cB cL cT algAL M loc
    i j hi E' F G e f g hE' hF hG he x
  calc
    @Equiv.toFun L T
        (@RingEquiv.toEquiv L T oldMulL oldMulT oldAddL oldAddT E) (F x) =
        E' (F x) := (congrFun hfun (F x)).symm
    _ = G (E' x) := hcomm
    _ = G (@Equiv.toFun L T
        (@RingEquiv.toEquiv L T oldMulL oldMulT oldAddL oldAddT E) x) :=
      congrArg G (congrFun hfun x)

end JoshiTeich.Act1Scene1.LocalizationFrobeniusNaturality
