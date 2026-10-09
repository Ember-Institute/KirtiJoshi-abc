import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaOddSupportBaseChange

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open IsDedekindDomain.HeightOneSpectrum
open NumberField
open WithZero
open scoped NumberField Valued

universe u

/-!
source-id: IUT-COR312-ODD-SUPPORT-Q-ORDER-BASE-CHANGE
source: `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/EmbedCompletion.lean`,
`valued_embedCompletion`; `refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`,
`tateFamilyOfTorsion`; completion order and relative ramification are ported in
`IutCompletionSource.lean` and `Prologue/Arithmetic/BaseChange.lean`.
fidelity: proves that completion q-order scales by the relative ramification
index, then applies the formula to the actual Tate family over the full odd
multiplicative support. This is a local order formula; it does not identify
the paper's selected `L'`-place sum with the weighted `F`-place sum.
boundary: Scene1/Derived
-/

private theorem iutCompletionQOrder_eq_relRamIdx_mul_of_eq_embed
    {F Kt : Type u} [Field F] [NumberField F] [Field Kt] [NumberField Kt]
    [Algebra F Kt]
    {v : NumberField.FinitePlace Kt} {w : NumberField.FinitePlace F}
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (q : w.maximalIdeal.adicCompletion F)
    (q' : v.maximalIdeal.adicCompletion Kt)
    (hq : q ≠ 0) (hqNorm : ‖q‖ < 1)
    (hq' : q' ≠ 0) (hqNorm' : ‖q'‖ < 1)
    (hqEq : q' = iutEmbedCompletion hvw q) :
    iutCompletionQOrder v q' =
      iutRelativeRamificationIndex (v := v) (w := w) *
        iutCompletionQOrder w q := by
  let e := iutRelativeRamificationIndex (v := v) (w := w)
  have hqVal := iutCompletionQOrder_valued w q hq hqNorm
  have hq'Val : Valued.v q' = exp
      (-((iutCompletionQOrder w q : ℤ) * (e : ℤ))) := by
    calc
      Valued.v q' = Valued.v (iutEmbedCompletion hvw q) := congrArg Valued.v hqEq
      _ = Valued.v q ^ e := iutValuedEmbedCompletion hvw q
      _ = exp (-((iutCompletionQOrder w q : ℤ) * (e : ℤ))) := by
        rw [hqVal, ← exp_nsmul, nsmul_eq_mul]
        ring_nf
  have hq'Val' := iutCompletionQOrder_valued v q' hq' hqNorm'
  have hInt : -(iutCompletionQOrder v q' : ℤ) =
      -((iutCompletionQOrder w q : ℤ) * (e : ℤ)) :=
    WithZero.exp_injective (hq'Val'.symm.trans hq'Val)
  have hInt' : (iutCompletionQOrder v q' : ℤ) =
      (iutCompletionQOrder w q : ℤ) * (e : ℤ) :=
    by omega
  calc
    iutCompletionQOrder v q' = iutCompletionQOrder w q * e := by
      exact_mod_cast hInt'
    _ = e * iutCompletionQOrder w q := Nat.mul_comm _ _

theorem iutInitialThetaOddSupportTateFamily_qOrder_eq_relRamIdx_mul
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : iutBadPlacesOverFinset (k := D.F)
      (K := ↥D.prime.torsionField)
      (iutInitialThetaOddSupportBaseQPilotSource D).badPlaces
      (iutInitialThetaOddSupportBaseQPilotSource D).badPlaces_finite) :
    iutCompletionQOrder w.1
        (((iutInitialThetaTateFamilyOfTorsion D).S w.1
          (iutInitialThetaOddSupportTateFamily_badPlace_source D w)).t.q) =
      iutRelativeRamificationIndex
          (v := w.1)
          (w := (IutTorsionQRootSource.basePlaceOf
            (B := iutInitialThetaOddSupportBaseQPilotSource D) w).1) *
        (iutInitialThetaOddSupportBaseQPilotSource D).qOrder
          (IutTorsionQRootSource.basePlaceOf
            (B := iutInitialThetaOddSupportBaseQPilotSource D) w) := by
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  let b := IutTorsionQRootSource.basePlaceOf (B := B) w
  let hvw := IutTorsionQRootSource.basePlaceOf_liesOver (B := B) w
  let hBad := iutInitialThetaOddSupportTateFamily_badPlace_source D w
  let S := (iutInitialThetaTateFamilyOfTorsion D).S w.1 hBad
  have hq : (S.t.q : w.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) =
      iutEmbedCompletion hvw (B.tateParameter b) := by
    simpa [B, b, hvw, hBad, S] using
      iutInitialThetaOddSupportTateFamily_q_eq_baseParameter D w
  change iutCompletionQOrder w.1 S.t.q =
    iutRelativeRamificationIndex (v := w.1) (w := b.1) *
      iutCompletionQOrder b.1 (B.tateParameter b)
  exact iutCompletionQOrder_eq_relRamIdx_mul_of_eq_embed hvw
    (B.tateParameter b) S.t.q
    (B.tateParameter_ne_zero b) (B.tateParameter_norm_lt_one b)
    S.t.q.ne_zero S.t.norm_lt_one hq

end JoshiTeich.Act1Scene1
