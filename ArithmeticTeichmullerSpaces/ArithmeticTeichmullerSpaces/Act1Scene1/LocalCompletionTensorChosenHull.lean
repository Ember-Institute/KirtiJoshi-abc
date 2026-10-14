import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorBoundedHull

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-CHOSEN-LEAST-HULL
source: actual bounded positive-Haar least principal hull existence;
Joshi III hull monotonicity in le:volume-lemma3 (3576--3583).
fidelity: chooses an actual least principal normalization region, proves
its topology, leastness, uniqueness as a set, monotonicity and fixed points.
The scalar multiplier can vary; the region is determined by leastness.
No paper theta locus or volume identification is assumed.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet
open MeasureTheory
open scoped Classical
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

def hullMultiplier (U : Set P.Tensor) (hU : Bornology.IsBounded U)
    (hpos : 0 < P.normalizationHaar U) : P.Tensor :=
  (P.exists_least_positiveHaar_hull U hU hpos).choose

def leastHull (U : Set P.Tensor) (hU : Bornology.IsBounded U)
    (hpos : 0 < P.normalizationHaar U) : Set P.Tensor :=
  P.principalRegion (P.hullMultiplier U hU hpos)

theorem hullMultiplier_isUnit (U : Set P.Tensor) (hU : Bornology.IsBounded U)
    (hpos : 0 < P.normalizationHaar U) : IsUnit (P.hullMultiplier U hU hpos) :=
  (P.exists_least_positiveHaar_hull U hU hpos).choose_spec.1

theorem subset_leastHull (U : Set P.Tensor) (hU : Bornology.IsBounded U)
    (hpos : 0 < P.normalizationHaar U) : U ⊆ P.leastHull U hU hpos :=
  (P.exists_least_positiveHaar_hull U hU hpos).choose_spec.2.1

theorem leastHull_isCompact (U : Set P.Tensor) (hU : Bornology.IsBounded U)
    (hpos : 0 < P.normalizationHaar U) : IsCompact (P.leastHull U hU hpos) :=
  P.principalRegion_isCompact _ (P.hullMultiplier_isUnit U hU hpos)

theorem leastHull_isOpen (U : Set P.Tensor) (hU : Bornology.IsBounded U)
    (hpos : 0 < P.normalizationHaar U) : IsOpen (P.leastHull U hU hpos) :=
  P.principalRegion_isOpen _ (P.hullMultiplier_isUnit U hU hpos)

theorem leastHull_haar_pos_lt_top (U : Set P.Tensor) (hU : Bornology.IsBounded U)
    (hpos : 0 < P.normalizationHaar U) :
    0 < P.normalizationHaar (P.leastHull U hU hpos) ∧
      P.normalizationHaar (P.leastHull U hU hpos) < ⊤ :=
  P.principalRegion_haar_pos_lt_top _ (P.hullMultiplier_isUnit U hU hpos)

theorem leastHull_le_principalRegion (U : Set P.Tensor) (hU : Bornology.IsBounded U)
    (hpos : 0 < P.normalizationHaar U) (a : P.Tensor) (ha : IsUnit a)
    (hUa : U ⊆ P.principalRegion a) : P.leastHull U hU hpos ⊆ P.principalRegion a :=
  (P.exists_least_positiveHaar_hull U hU hpos).choose_spec.2.2.2.2.2 a ha hUa

theorem leastHull_mono {U V : Set P.Tensor}
    (hU : Bornology.IsBounded U) (hUpos : 0 < P.normalizationHaar U)
    (hV : Bornology.IsBounded V) (hVpos : 0 < P.normalizationHaar V) (hUV : U ⊆ V) :
    P.leastHull U hU hUpos ⊆ P.leastHull V hV hVpos :=
  P.leastHull_le_principalRegion U hU hUpos _ (P.hullMultiplier_isUnit V hV hVpos)
    (hUV.trans (P.subset_leastHull V hV hVpos))

theorem leastHull_eq_of_principal_minimal (U : Set P.Tensor) (hU : Bornology.IsBounded U)
    (hpos : 0 < P.normalizationHaar U) (a : P.Tensor) (ha : IsUnit a)
    (hUa : U ⊆ P.principalRegion a)
    (hmin : ∀ b : P.Tensor, IsUnit b → U ⊆ P.principalRegion b →
      P.principalRegion a ⊆ P.principalRegion b) :
    P.leastHull U hU hpos = P.principalRegion a :=
  Set.Subset.antisymm (P.leastHull_le_principalRegion U hU hpos a ha hUa)
    (hmin _ (P.hullMultiplier_isUnit U hU hpos) (P.subset_leastHull U hU hpos))

theorem leastHull_principalRegion (a : P.Tensor) (ha : IsUnit a) :
    P.leastHull (P.principalRegion a) (P.principalRegion_isCompact a ha).isBounded
      (P.principalRegion_haar_pos_lt_top a ha).1 = P.principalRegion a :=
  Set.Subset.antisymm
    (P.leastHull_le_principalRegion _ _ _ a ha Set.Subset.rfl) (P.subset_leastHull _ _ _)

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet
