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

The Prologue deliberately stores the q parameter and Tate data as separate
carriers.  This module records the exact compatibility needed by the q-family
bridge and derives the strict q-norm range from the already explicit Tate laws.
-/

structure QNormTateCompatibility
    {K : Type uK} [Field K] [NumberField K]
    (D : AdelicThetaLinkData K) : Prop where
  places_eq : D.places = D.tate.places
  norm_eq : ∀ w ∈ D.places, D.qNorm w = D.tate.norm w

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
  · rw [hCompat.norm_eq w hw]
    exact hTate.norm_pos w hwTate
  · rw [hCompat.norm_eq w hw]
    exact hTate.norm_lt_one w hwTate

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

end JoshiTeich.Act1Scene1
