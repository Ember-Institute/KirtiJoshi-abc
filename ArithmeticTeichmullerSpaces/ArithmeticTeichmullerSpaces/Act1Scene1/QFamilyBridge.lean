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

/-!
This is the finite-support adapter available before the paper's
`V_p^oss` construction is realized.  It filters the already supplied finite
place carrier by residue characteristic; the ideal-over characterization below
keeps the rational-prime label explicit without claiming the source bad-place
construction has been completed.
-/
noncomputable def Corollary312SourcePlacesOver
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) (q : ℕ) :
    Finset (NumberField.FinitePlace K) :=
  T.scene1.data.link.places.filter (fun w => Arithmetic.residueChar w = q)

lemma mem_sourcePlacesOver_iff
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p q : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) (w : NumberField.FinitePlace K) :
    w ∈ Corollary312SourcePlacesOver p T q ↔
      w ∈ T.scene1.data.link.places ∧ Arithmetic.residueChar w = q := by
  simp [Corollary312SourcePlacesOver]

lemma mem_sourcePlacesOver_iff_liesOver
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p q : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (hq : q.Prime) (T : Corollary312Data K O p)
    (w : NumberField.FinitePlace K) :
    w ∈ Corollary312SourcePlacesOver p T q ↔
      w ∈ T.scene1.data.link.places ∧
        Ideal.LiesOver w.maximalIdeal.asIdeal
          (Ideal.span {(q : ℤ)}) := by
  rw [mem_sourcePlacesOver_iff p q T w]
  constructor
  · rintro ⟨hw, hq_char⟩
    exact ⟨hw, hq_char ▸ Arithmetic.residueChar_liesOver w⟩
  · rintro ⟨hw, hwq⟩
    refine ⟨hw, ?_⟩
    apply (Arithmetic.natCast_mem_maximalIdeal_iff w hq).mp
    have hq_mem : (q : ℤ) ∈ Ideal.span {(q : ℤ)} := by
      exact Ideal.mem_span_singleton.mpr ⟨1, by simp⟩
    simpa using (Ideal.mem_of_liesOver (P := w.maximalIdeal.asIdeal)
      (p := Ideal.span {(q : ℤ)}) (q : ℤ)).mp hq_mem

/-!
The source-side q-family uses exactly the finite-place filter above.  These
two lemmas consume the Prologue arithmetic adapter without identifying this
carrier with the paper's `V_p^oss`; that identification remains a separate
Initial Theta Data obligation.
-/
lemma sourcePlacesOver_localDeg_sum_le_finrank
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p q : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (hq : q.Prime) (T : Corollary312Data K O p) :
    ∑ w ∈ Corollary312SourcePlacesOver p T q, Arithmetic.localDeg w ≤
      Module.finrank ℚ K := by
  simpa [Corollary312SourcePlacesOver] using
    (Arithmetic.localDeg_sum_le_finrank_of_residueChar_filter
      T.scene1.data.link.places q hq)

lemma sourcePlacesOver_qPilotWeight_sum_le_one
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p q : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (hq : q.Prime) (T : Corollary312Data K O p) :
    ∑ w ∈ Corollary312SourcePlacesOver p T q, Arithmetic.qPilotWeight w ≤ 1 := by
  simpa [Corollary312SourcePlacesOver] using
    (Arithmetic.qPilotWeight_sum_le_one_of_residueChar_filter
      T.scene1.data.link.places q hq)

/-!
The paper writes the finite q-family as pairs `(p,w)` with a rational prime
`p` and a finite place `w`.  The place subtype above remains the target's
local carrier; this structure makes the rational-prime label and the finite
pair indexing explicit before a real Initial Theta Data construction is
available.
-/
structure Corollary312SourceQPair
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) where
  rationalPrime : ℕ
  rationalPrime_prime : Nat.Prime rationalPrime
  place : Corollary312SourceQIndex p T
  rationalPrime_eq_residueChar :
    rationalPrime = Arithmetic.residueChar place.1
  /-- The finite place lies over the rational prime ideal labelled by the pair. -/
  rationalPrime_liesOver :
    Ideal.LiesOver place.1.maximalIdeal.asIdeal
      (Ideal.span {(rationalPrime : ℤ)})
  /-- The source pair is represented by a place carrying a Tate parameter. -/
  tate_place : place.1 ∈ T.scene1.data.link.tate.places
  /-- Coprimality of `ell` with the normalized Tate q-order, ported from
  `AdmissiblePrimeData.q_order_coprime` in `iut`. -/
  q_order_coprime : Nat.Coprime T.ell (T.scene1.data.link.tate.qOrder place.1)

namespace Corollary312SourceQPair

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data K O p}

/-- The normalized Tate q-order attached to the pair's finite place.  This is the
`AdmissiblePrimeData.qOrder` projection in `iut`, with the external ordered Tate
parameter replaced by the Prologue carrier's `orderNat` field. -/
noncomputable def qOrder (self : Corollary312SourceQPair p T) : ℕ :=
  T.scene1.data.link.tate.qOrder self.place.1

lemma qOrder_pos (self : Corollary312SourceQPair p T) : 0 < self.qOrder p := by
  unfold qOrder
  exact T.scene1.input_laws.tate_parameter.orderNat_pos self.place.1 self.tate_place

end Corollary312SourceQPair

structure Corollary312SourceQGrouping
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p) where
  pair : Type uK
  pairFintype : Fintype pair
  pairData : pair → Corollary312SourceQPair p T
  indexEquiv : T.qIndex ≃ pair

noncomputable def Corollary312GroupedSourceQFactor
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (G : Corollary312SourceQGrouping p T)
    (i : G.pair) : ℝ :=
  (T.scene1.data.link.qNorm (G.pairData i).place.1) ^ (1 / (2 * (T.ell : ℝ)))

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
