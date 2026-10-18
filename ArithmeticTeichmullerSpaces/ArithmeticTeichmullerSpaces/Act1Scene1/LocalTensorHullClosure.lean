import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionTensorSaturatedLogShell
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalArchimedeanTensorRadialHull
import Mathlib.Order.Closure

/-!
source-id: JT-SCENE1-LOCAL-TENSOR-HULL-CLOSURE
source: reference Cor312/HolomorphicHull, closureOperator and hull_idem;
Joshi III principal hull (3568--3574) and le:volume-lemma3.
fidelity: the already constructed least principal/radial hulls form genuine
Mathlib closure operators on bounded positive-Haar regions. Integral and
saturated-shell fixed points are proved from actual hulls, not postulated.
The archimedean class remains positive radial regions. No paper locus/hull
identity is asserted. Original consumer proofs; no reference source copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion.Packet

open MeasureTheory
open scoped Classical Pointwise
universe u
noncomputable section
variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] (P : Packet K p ι)

abbrev AdmissibleHullRegion :=
  {U : Set P.Tensor // Bornology.IsBounded U ∧ 0 < P.normalizationHaar U}

def hullRegion (U : P.AdmissibleHullRegion) : P.AdmissibleHullRegion :=
  ⟨P.leastHull U.1 U.2.1 U.2.2, (P.leastHull_isCompact _ _ _).isBounded,
    (P.leastHull_haar_pos_lt_top _ _ _).1⟩

theorem hullRegion_idem (U : P.AdmissibleHullRegion) :
    P.hullRegion (P.hullRegion U) = P.hullRegion U := by
  apply Subtype.ext
  exact P.leastHull_principalRegion _ (P.hullMultiplier_isUnit U.1 U.2.1 U.2.2)

def hullClosure : ClosureOperator P.AdmissibleHullRegion where
  toFun := P.hullRegion
  monotone' U V hUV := P.leastHull_mono U.2.1 U.2.2 V.2.1 V.2.2 hUV
  le_closure' U := P.subset_leastHull _ _ _
  idempotent' := P.hullRegion_idem

theorem hullClosure_isClosed_iff (U : P.AdmissibleHullRegion) :
    P.hullClosure.IsClosed U ↔ ∃ a : P.Tensor, IsUnit a ∧ U.1 = P.principalRegion a := by
  constructor
  · intro h
    have he : (P.hullRegion U).1 = U.1 := congrArg Subtype.val h.closure_eq
    exact ⟨_, P.hullMultiplier_isUnit U.1 U.2.1 U.2.2, he.symm⟩
  · rintro ⟨a, ha, he⟩
    apply (P.hullClosure).isClosed_iff.mpr
    apply Subtype.ext
    change P.leastHull U.1 U.2.1 U.2.2 = U.1
    apply Set.Subset.antisymm
    · intro x hx
      rw [he]
      exact P.leastHull_le_principalRegion U.1 U.2.1 U.2.2 a ha (by rw [he]) hx
    · exact P.subset_leastHull _ _ _

def integralHullRegion : P.AdmissibleHullRegion :=
  ⟨P.normalization, P.normalization_isCompact.isBounded,
    by rw [P.normalizationHaar_normalization]; exact zero_lt_one⟩

theorem hullClosure_integralHullRegion : P.hullClosure P.integralHullRegion = P.integralHullRegion := by
  apply (P.hullClosure_isClosed_iff _).mpr ?_ |>.closure_eq
  refine ⟨1, isUnit_one, ?_⟩
  change (P.normalization : Set P.Tensor) = P.principalRegion 1
  simp [principalRegion]

def saturatedShellHullRegion : P.AdmissibleHullRegion :=
  ⟨P.saturatedLogShell, P.saturatedLogShell_isCompact.isBounded,
    P.saturatedLogShell_haar_pos_lt_top.1⟩

theorem hullClosure_saturatedShellHullRegion :
    P.hullClosure P.saturatedShellHullRegion = P.saturatedShellHullRegion := by
  apply (P.hullClosure_isClosed_iff _).mpr ?_ |>.closure_eq
  refine ⟨P.hullMultiplier P.tensorLogShell P.tensorLogShell_isBounded P.tensorLogShell_haar_pos,
    P.hullMultiplier_isUnit P.tensorLogShell P.tensorLogShell_isBounded P.tensorLogShell_haar_pos, ?_⟩
  exact P.saturatedLogShell_eq_leastHull

end
end JoshiTeich.Act1Scene1.LocalCompletion.Packet

namespace JoshiTeich.Act1Scene1.LocalArchimedean

open NumberField MeasureTheory
open scoped Classical Pointwise
universe u
noncomputable section
variable {K : Type u} [Field K] {ι : Type} [Fintype ι] (c : ι → InfinitePlace K)

abbrev AdmissibleHullRegion :=
  {U : Set (Tensor c) // Bornology.IsBounded U ∧ 0 < normalizedHaar c U}

def hullRegion (U : AdmissibleHullRegion c) : AdmissibleHullRegion c :=
  ⟨radialHull c U.1, (radialHull_isCompact c _).isBounded,
    (radialHull_haar_pos_lt_top c U.2.1 U.2.2).1⟩

def hullClosure : ClosureOperator (AdmissibleHullRegion c) where
  toFun := hullRegion c
  monotone' U V hUV := radialHull_mono c U.2.1 U.2.2 V.2.1 V.2.2 hUV
  le_closure' U := subset_radialHull c U.2.1 U.2.2
  idempotent' U := Subtype.ext (radialHull_idem c U.2.1 U.2.2)

theorem hullClosure_isClosed_iff (U : AdmissibleHullRegion c) :
    (hullClosure c).IsClosed U ↔ ∃ t : ℝ, 0 < t ∧ U.1 = radialRegion c t := by
  constructor
  · intro h
    have he : (hullRegion c U).1 = U.1 := congrArg Subtype.val h.closure_eq
    exact ⟨_, hullRadius_pos c U.2.1 U.2.2, he.symm⟩
  · rintro ⟨t, ht, he⟩
    apply (hullClosure c).isClosed_iff.mpr
    apply Subtype.ext
    change radialHull c U.1 = U.1
    rw [he, radialHull_radialRegion c ht]

def integralHullRegion : AdmissibleHullRegion c :=
  ⟨archIntegral c, (isCompact_archIntegral c).isBounded,
    by rw [normalizedHaar_archIntegral]; exact zero_lt_one⟩

theorem hullClosure_integralHullRegion :
    hullClosure c (integralHullRegion c) = integralHullRegion c := by
  apply (hullClosure_isClosed_iff c _).mpr ?_ |>.closure_eq
  exact ⟨1, zero_lt_one, (one_smul ℝ (archIntegral c)).symm⟩

def logShellHullRegion : AdmissibleHullRegion c :=
  ⟨archLogShell c, (isCompact_archLogShell c).isBounded, (archLogShell_haar_pos_lt_top c).1⟩

theorem hullClosure_logShellHullRegion :
    hullClosure c (logShellHullRegion c) = logShellHullRegion c := by
  apply Subtype.ext
  exact radialHull_archLogShell c

end
end JoshiTeich.Act1Scene1.LocalArchimedean
