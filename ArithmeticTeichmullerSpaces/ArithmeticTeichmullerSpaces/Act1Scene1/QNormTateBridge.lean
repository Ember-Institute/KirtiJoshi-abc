import ArithmeticTeichmullerSpaces.Act1Scene1.QFamilyBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe uK

/-!
source-id: JT-ATS-III-SCENE1-QNORM-TATE
source: `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.md`,
`th:tate-parameter-as-a-function` (609--630); supplementary source:
`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`pr:admissible-lifts-tate-params` (1530--1539)
fidelity: Scene1 compatibility bridge between the q-norm carrier and the Tate
parameter carrier; equality of the two local norm functions is explicit and is
not added to Prologue/Core
boundary: Scene1/Derived

The Prologue stores the local q-parameter function and the Tate data as separate
carriers.  This module records the place identification and local parameter
compatibility needed by the q-family bridge.  The norm equality is derived from
that compatibility and the explicit Tate laws.
-/

structure QNormTateCompatibility
    {K : Type uK} [Field K] [NumberField K]
    (D : AdelicThetaLinkData K) : Prop where
  places_eq : D.places = D.tate.places
  parameter_eq : ∀ w ∈ D.places, D.qParameter w = D.tate.parameter w

theorem qNormTateCompatibility_of_tateParameters
    {K : Type uK} [Field K] [NumberField K]
    (tate : Theta.TateParameterData K)
    (theta : ThetaPilotData K)
    (thetaBase : theta.index)
    (packetHull : PacketHullData theta.index)
    (heightData : Arithmetic.HeightData K)
    (ramification : Arithmetic.RamificationProfile K)
    (logVolume : ℝ)
    (processionLength : ℕ) :
    QNormTateCompatibility
      (AdelicThetaLinkData.ofTateParameters tate theta thetaBase packetHull
        heightData ramification logVolume processionLength) := by
  constructor
  · rfl
  · intro w hw
    rfl

theorem QNormTateCompatibility.norm_eq
    {K : Type uK} [Field K] [NumberField K]
    (D : AdelicThetaLinkData K)
    (hTate : Theta.TateParameterLaws D.tate)
    (hCompat : QNormTateCompatibility D) :
    ∀ w ∈ D.places, D.qNorm w = D.tate.norm w := by
  intro w hw
  have hwTate : w ∈ D.tate.places := by
    rw [← hCompat.places_eq]
    exact hw
  change ‖D.qParameter w‖ = D.tate.norm w
  rw [hCompat.parameter_eq w hw]
  exact (hTate.norm_eq w hwTate).symm

theorem qNorm_pos_lt_one_of_tate
    {K : Type uK} [Field K] [NumberField K]
    (D : AdelicThetaLinkData K)
    (hTate : Theta.TateParameterLaws D.tate)
    (hCompat : QNormTateCompatibility D) :
    ∀ w ∈ D.places, 0 < D.qNorm w ∧ D.qNorm w < 1 := by
  intro w hw
  have hwTate : w ∈ D.tate.places := by
    rw [← hCompat.places_eq]
    exact hw
  constructor
  · rw [hCompat.norm_eq D hTate w hw]
    exact hTate.norm_pos w hwTate
  · rw [hCompat.norm_eq D hTate w hw]
    exact hTate.norm_lt_one w hwTate

/-!
The normalized-order file in `TateCurvesTheta` identifies the norm of `q` with
the corresponding power of a uniformizer norm.  The local project does not yet
carry the uniformizer/valuation construction, so the identification is an
explicit Scene1 compatibility proposition.  The logarithmic consequences are
proved here and can be consumed by the q-family accounting once that
compatibility is constructed.
-/
structure TateOrderNormCompatibility
    {K : Type uK} [Field K] [NumberField K]
    (D : AdelicThetaLinkData K) : Type uK where
  uniformizerNorm : NumberField.FinitePlace K → ℝ
  uniformizerNorm_pos : ∀ w ∈ D.places, 0 < uniformizerNorm w
  uniformizerNorm_lt_one : ∀ w ∈ D.places, uniformizerNorm w < 1
  norm_eq_pow_order : ∀ w ∈ D.places,
    D.tate.norm w = uniformizerNorm w ^ D.tate.qOrder w

theorem TateOrderNormCompatibility.qNorm_log_eq_order_mul
    {K : Type uK} [Field K] [NumberField K]
    (D : AdelicThetaLinkData K)
    (hTate : Theta.TateParameterLaws D.tate)
    (hCompat : QNormTateCompatibility D)
    (hOrder : TateOrderNormCompatibility D) :
    ∀ w ∈ D.places,
      -Real.log (D.qNorm w) =
        (D.tate.qOrder w : ℝ) * -Real.log (hOrder.uniformizerNorm w) := by
  intro w hw
  rw [hCompat.norm_eq D hTate w hw, hOrder.norm_eq_pow_order w hw, Real.log_pow]
  push_cast
  ring

theorem TateOrderNormCompatibility.qFactor_log_eq_order_mul
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p ell : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : AdelicThetaLinkData K)
    (hTate : Theta.TateParameterLaws D.tate)
    (hCompat : QNormTateCompatibility D)
    (hOrder : TateOrderNormCompatibility D)
    (hEll : 0 < ell) :
    ∀ w ∈ D.places,
      -Real.log (D.qNorm w ^ (1 / (2 * (ell : ℝ)))) =
        (1 / (2 * (ell : ℝ))) *
          ((D.tate.qOrder w : ℝ) * -Real.log (hOrder.uniformizerNorm w)) := by
  intro w hw
  have hq : 0 < D.qNorm w := (qNorm_pos_lt_one_of_tate D hTate hCompat w hw).1
  rw [Real.log_rpow hq, hCompat.norm_eq D hTate w hw,
    hOrder.norm_eq_pow_order w hw, Real.log_pow]
  push_cast
  ring

theorem TateOrderNormCompatibility.groupedSourceQFactor_log_eq_order_mul
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (G : Corollary312SourceQGrouping p T)
    (hTate : Theta.TateParameterLaws T.scene1.data.link.tate)
    (hCompat : QNormTateCompatibility T.scene1.data.link)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hEll : 0 < T.ell) :
    ∀ i, -Real.log (Corollary312GroupedSourceQFactor p T G i) =
      (1 / (2 * (T.ell : ℝ))) *
        ((T.scene1.data.link.tate.qOrder (G.pairData i).place.1 : ℝ) *
          -Real.log (hOrder.uniformizerNorm (G.pairData i).place.1)) := by
  intro i
  simpa [Corollary312GroupedSourceQFactor] using
    TateOrderNormCompatibility.qFactor_log_eq_order_mul (K := K) (O := O)
      p T.ell T.scene1.data.link
      hTate hCompat hOrder hEll
      (G.pairData i).place.1 (G.pairData i).place.2

def Corollary312QFamily.ofTateCompatibility
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (V : Corollary312VolumeData p T)
    (hCompat : QNormTateCompatibility T.scene1.data.link)
    (indexEquiv : T.qIndex ≃ Corollary312SourceQIndex p T)
    (qFactor_eq : ∀ i, V.qFactor i =
      Corollary312SourceQFactor p T (indexEquiv i))
    (qLogTerm_eq : ∀ i, T.qLogTerm i =
      -Real.log (Corollary312SourceQFactor p T (indexEquiv i))) :
    Corollary312QFamily p T V := by
  have hRange := qNorm_pos_lt_one_of_tate T.scene1.data.link
    T.scene1.input_laws.tate_parameter hCompat
  refine
    { indexEquiv := indexEquiv
      qNorm_le_one := ?_
      qFactor_eq := qFactor_eq
      qLogTerm_eq := qLogTerm_eq }
  intro w
  exact (hRange w.1 w.2).2.le

/-!
This carrier is the public Scene1 assembly form for a q-family obtained from
the Tate parameter data.  It keeps the compatibility proof and the source
index/equality data visible, while deriving `qNorm_le_one` through
`ofTateCompatibility` instead of accepting that bound as an unrelated field.
-/
structure Corollary312TateQFamily
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (V : Corollary312VolumeData p T) where
  compatibility : QNormTateCompatibility T.scene1.data.link
  grouping : Corollary312SourceQGrouping p T
  indexEquiv : T.qIndex ≃ Corollary312SourceQIndex p T
  grouping_place_eq : ∀ i,
    (grouping.pairData (grouping.indexEquiv i)).place = indexEquiv i
  qFactor_eq : ∀ i, V.qFactor i =
    Corollary312SourceQFactor p T (indexEquiv i)
  qLogTerm_eq : ∀ i, T.qLogTerm i =
    -Real.log (Corollary312SourceQFactor p T (indexEquiv i))

def Corollary312TateQFamily.toQFamily
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data K O p}
    {V : Corollary312VolumeData p T}
    (Q : Corollary312TateQFamily p T V) :
    Corollary312QFamily p T V :=
  Corollary312QFamily.ofTateCompatibility p T V Q.compatibility Q.indexEquiv
    Q.qFactor_eq Q.qLogTerm_eq

end JoshiTeich.Act1Scene1
