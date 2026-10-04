import ArithmeticTeichmullerSpaces.Act1Scene1.VolumeBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe uK

/-!
source-id: JT-ATS-III-SCENE1-Q-FAMILY
source: `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`,
`th:moccor-Mochizuki-form2` (3617--3632) and `cor:cor312` (3647--3650)
fidelity: Scene1 q-family normalization and finite-index identification;
the paper's `(p,w)` grouping is represented by an explicit equivalence to the
finite place index and is not inferred from an unproved global construction
boundary: Scene1/Derived

The source q-family is kept separate from `Corollary312Data`: this module makes
the identification and normalization visible before it is consumed by the
analytic volume bridge.
-/

def Corollary312SourceQIndex
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) : Type uK :=
  {w // w ∈ T.scene1.data.link.places}

noncomputable def Corollary312SourceQFactor
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (i : Corollary312SourceQIndex p T) : ℝ :=
  (T.scene1.data.link.qNorm i.1) ^ (1 / (2 * (T.ell : ℝ)))

structure Corollary312QFamily
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (V : Corollary312VolumeData p T) where
  indexEquiv : T.qIndex ≃ Corollary312SourceQIndex p T
  qNorm_le_one : ∀ w : Corollary312SourceQIndex p T,
    T.scene1.data.link.qNorm w.1 ≤ 1
  qFactor_eq : ∀ i, V.qFactor i =
    Corollary312SourceQFactor p T (indexEquiv i)
  qLogTerm_eq : ∀ i, T.qLogTerm i =
    -Real.log (Corollary312SourceQFactor p T (indexEquiv i))

theorem Corollary312QFamily.qFactor_pos
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data K O p}
    {V : Corollary312VolumeData p T}
    (Q : Corollary312QFamily p T V) :
    ∀ i, 0 < V.qFactor i := by
  intro i
  rw [Q.qFactor_eq i]
  unfold Corollary312SourceQFactor
  apply Real.rpow_pos_of_pos
  exact T.scene1.input_laws.first_axiom.q_norm_positive
    (Q.indexEquiv i).1 (Q.indexEquiv i).2

theorem Corollary312QFamily.qFactor_le_one
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data K O p}
    {V : Corollary312VolumeData p T}
    (hSide : Corollary312SideConditions p T)
    (Q : Corollary312QFamily p T V) :
    ∀ i, V.qFactor i ≤ 1 := by
  intro i
  rw [Q.qFactor_eq i]
  unfold Corollary312SourceQFactor
  apply Real.rpow_le_one
  · exact (T.scene1.input_laws.first_axiom.q_norm_positive
      (Q.indexEquiv i).1 (Q.indexEquiv i).2).le
  · exact Q.qNorm_le_one (Q.indexEquiv i)
  · have hEll : 0 < (T.ell : ℝ) :=
      Nat.cast_pos.mpr hSide.ell_prime.pos
    exact one_div_nonneg.mpr (by positivity : 0 ≤ 2 * (T.ell : ℝ))

theorem Corollary312QFamily.qLogTerm_source
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data K O p}
    {V : Corollary312VolumeData p T}
    (Q : Corollary312QFamily p T V) :
    ∀ i, T.qLogTerm i = -Real.log (V.qFactor i) := by
  intro i
  rw [Q.qFactor_eq i]
  exact Q.qLogTerm_eq i

theorem volumeBound_of_qFamily
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (hSide : Corollary312SideConditions p T)
    (V : Corollary312VolumeData p T)
    (Q : Corollary312QFamily p T V)
    (hThetaVolume : T.thetaVolume ≤ 1)
    (hLower : T.thetaVolume ≥ Corollary312Data.qProduct p T V.qFactor) :
    Corollary312VolumeBound p T V := by
  exact
    { qFactor_pos := Corollary312QFamily.qFactor_pos p Q
      qFactor_le_one := Corollary312QFamily.qFactor_le_one p hSide Q
      qLogTerm_eq := Corollary312QFamily.qLogTerm_source p Q
      thetaVolume_le_one := hThetaVolume
      volume_lower_bound := hLower }

theorem corollary312_of_q_family_lower_bound
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (hSide : Corollary312SideConditions p T)
    (V : Corollary312VolumeData p T)
    (Q : Corollary312QFamily p T V)
    (hThetaVolume : T.thetaVolume ≤ 1)
    (hLower : T.thetaVolume ≥ Corollary312Data.qProduct p T V.qFactor) :
    Corollary312 p T := by
  apply corollary312_of_volume_lower_bound p T hSide V
  exact volumeBound_of_qFamily p T hSide V Q hThetaVolume hLower

end JoshiTeich.Act1Scene1
