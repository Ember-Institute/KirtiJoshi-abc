import ArithmeticTeichmullerSpaces.Act1Scene1.TransferQAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.QPilotTransferBridge

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe uK

/-!
source-id: JT-ATS-III-SCENE1-ADELIC-THETA-BRIDGE
source: `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`th:adelic-theta-link` (1139--1166), `pr:general-cohomology-set-const`
(3261--3271), `th:thetam-construction` (3296--3346), `le:volume-lemma3`
(3576--3583), and `cor:cor312` (3647--3650)
fidelity: public Scene1 assembly of independently typed target data,
q-family identification, volume normalization, and packet/hull accounting;
the source constructions remain explicit inputs and are not replaced by a
Prologue obligation constructor
boundary: Scene1/Derived

`Corollary312Scene1Data` keeps the construction outputs separate.  In
particular, it does not store `Corollary312` or an equivalent inequality as a
field.  The target is produced by composing the logarithmic, q-family, volume
normalization, and finite accounting lemmas.
-/

structure Corollary312Scene1Data
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O] where
  target : Corollary312Data K O p
  volume : Corollary312VolumeData p target
  qFamily : Corollary312TateQFamily p target volume
  normalization : Corollary312VolumeNormalization p target
  accounting : Corollary312TateQAccounting p target volume qFamily
  ell_prime : Nat.Prime target.ell
  ell_ge_five : 5 ≤ target.ell
  ellStar_eq_half_sub_one : target.ellStar = (target.ell - 1) / 2
  ellStar_pos : 0 < target.ellStar

/-!
The q-pilot route has additional construction obligations which are not part
of the generic Scene1 assembly.  Keeping them in a separate bundle makes the
route explicit: a caller must provide the Tate order/norm compatibility, the
local q-pilot normalization, and the finite source-index equivalence.
-/
structure Corollary312Scene1QPilotData
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O] where
  base : Corollary312Scene1Data (K := K) (O := O) p
  qPilot : Corollary312QPilotData p base.target
  orderCompatibility : TateOrderNormCompatibility base.target.scene1.data.link
  sourceNormalization :
    Corollary312QPilotSourceNormalization p base.target
      orderCompatibility qPilot
  sourceIndexBridge :
    Corollary312QPilotSourceIndexBridge p base.target base.volume qPilot
      base.qFamily

theorem cor312_of_adelicThetaLink
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : Corollary312Scene1Data (K := K) (O := O) p) :
    Corollary312 p D.target := by
  exact corollary312_of_transfer_q_accounting p D.target D.volume D.qFamily.toQFamily
    D.normalization D.accounting.toAccounting D.ell_prime D.ell_ge_five
    D.ellStar_eq_half_sub_one D.ellStar_pos

theorem cor312_of_adelicThetaLink_qPilot
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (D : Corollary312Scene1QPilotData (K := K) (O := O) p) :
    Corollary312 p D.base.target := by
  exact corollary312_of_qPilot_accounting p D.base.target D.base.volume
    D.base.qFamily D.base.normalization D.base.accounting D.qPilot
    D.orderCompatibility D.sourceNormalization D.base.ell_prime.pos
    D.sourceIndexBridge D.base.ell_prime D.base.ell_ge_five
    D.base.ellStar_eq_half_sub_one D.base.ellStar_pos

end JoshiTeich.Act1Scene1
