/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original paths Iut/Concrete/Container.lean, Iut/Cor312/PacketPresentation.lean, and Iut/Cor312/HolomorphicHull.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ContainerHull
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_LogVolume
import Solutions.Source_ReferenceIutConcreteFibers
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.NhdsWithin

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

universe u v

open NumberField
open scoped BigOperators Pointwise

namespace DirectSumPresentation

variable {C : Type u} (P : DirectSumPresentation.{u, v} C)

@[simp] lemma mem_integralRegion {x : P.Total} : x ∈ P.integralRegion ↔ ∀ c, x c ∈ P.integral c :=
  Iff.rfl

@[simp] lemma mem_productRegion {U : ∀ c, Set (P.Summand c)} {x : P.Total} :
    x ∈ P.productRegion U ↔ ∀ c, x c ∈ U c := Iff.rfl

lemma isProductRegion_productRegion (U : ∀ c, Set (P.Summand c)) :
    P.IsProductRegion (P.productRegion U) := ⟨U, rfl⟩

@[simp] lemma scaledIntegral_one : P.scaledIntegral (fun _ => 1) = P.integralRegion := by
  ext x
  simp [scaledIntegral, integralRegion]

lemma isHullRegion_integralRegion : P.IsHullRegion P.integralRegion :=
  ⟨fun _ => 1, fun _ => isUnit_one, (P.scaledIntegral_one).symm⟩

end DirectSumPresentation

/-- Constructor for hull systems from an existence certificate: given a class of
relatively compact admissible regions and a class `𝓗` of hull regions containing the
integral region, for which least members of `𝓗` containing each admissible region exist
and are again admissible, the choice of least hull regions is a hull system. This is the
seam through which the local-field project (taxis #4) discharges hull existence: the
`exists_least` field is exactly IUT III, Remark 3.9.5(i) for the given classes. -/
private noncomputable def hullSystemOfExists {C : Type u} (P : DirectSumPresentation.{u, v} C)
    (A : Set (Set P.Total)) (relCompact : ∀ U ∈ A, IsCompact (closure U))
    (𝓗 : Set (Set P.Total)) (isHullRegion_of_mem : ∀ R ∈ 𝓗, P.IsHullRegion R)
    (integralRegion_mem : P.integralRegion ∈ 𝓗)
    (exists_least : ∀ U ∈ A, ∃ R, P.IsLeastHullRegionIn 𝓗 U R)
    (least_admissible : ∀ U ∈ A, ∀ R, P.IsLeastHullRegionIn 𝓗 U R → R ∈ A) :
    HullSystem P where
  Admissible := A
  relCompact_of_admissible := relCompact
  HullRegions := 𝓗
  isHullRegion_of_mem := isHullRegion_of_mem
  integralRegion_mem := integralRegion_mem
  hull U := open Classical in
    if hU : U ∈ A then (exists_least U hU).choose else Set.univ
  isLeastHullRegion_hull U hU := by
    simpa [hU] using (exists_least U hU).choose_spec
  hull_admissible U hU := by
    simpa [hU] using least_admissible U hU _ (exists_least U hU).choose_spec

namespace LocalTheory

variable {K : Type u} [Field K] [NumberField K] (LT : LocalTheory.{u, v} K)

/-- The packet presentation at capsule labels `ι` and rational place `v_ℚ`. -/
noncomputable def packet (ι : Type) [Fintype ι] (vQ : RationalPlace) :
    DirectSumPresentation.{u, v} (ι → LT.Fiber vQ) where
  Summand c := LT.Tensor vQ (LT.tuple vQ c)
  integral c := LT.integral vQ (LT.tuple vQ c)

/-- A product region is a `Set.pi`. -/
lemma productRegion_eq_pi {C : Type*} (P : DirectSumPresentation C)
    (U : ∀ c, Set (P.Summand c)) : P.productRegion U = Set.pi Set.univ U := by
  ext x; exact ⟨fun h c _ => h c, fun h c => h c (Set.mem_univ c)⟩

/-- The closure of a product of relatively compact regions is compact. -/
lemma isCompact_closure_productRegion {C : Type*} (P : DirectSumPresentation C)
    (U : ∀ c, Set (P.Summand c)) (hU : ∀ c, IsCompact (closure (U c))) :
    IsCompact (closure (P.productRegion U)) := by
  rw [productRegion_eq_pi]
  change IsCompact (closure (Set.pi Set.univ U : Set (∀ c, P.Summand c)))
  rw [closure_pi_set]
  exact isCompact_univ_pi hU

/-- **The concrete large volume container** for the standard procession of length `n`
(IUT III, Propositions 3.1–3.3). -/
noncomputable def container (n : ℕ) : LargeVolumeContainerData.{0, u, v} ℕ (Place K) where
  proc := Procession.standard n
  toRational := LT.toRational
  fiberFintype vQ := LT.fiberFintype vQ
  packet i vQ := LT.packet ((Procession.standard n).capsule i).LabelType vQ
  logShell i vQ := (LT.packet _ vQ).productRegion fun c => LT.logShell vQ (LT.tuple vQ c)
  logShell_isProduct i vQ := DirectSumPresentation.isProductRegion_productRegion _ _
  logShell_relCompact i vQ :=
    isCompact_closure_productRegion _ _ fun c => LT.logShell_relCompact vQ _
  logShell_finiteSupport i := by
    -- outside `∞`, `2` and the primes ramified in `K`, the log-shell is the integral
    -- structure
    have hfin : (({RationalPlace.infinite} ∪ {RationalPlace.finite ⟨2, Nat.prime_two⟩} ∪
        ((fun w => LT.toRational (Place.finite w)) '' {w | ramIdx K w ≠ 1}) :
          Set RationalPlace)).Finite :=
      ((Set.finite_singleton _).union (Set.finite_singleton _)).union
        (LT.ramified_finite.image _)
    refine hfin.subset fun vQ hvQ => ?_
    by_contra hmem
    apply hvQ
    rcases vQ with p | _
    · have hp2 : (p : ℕ) ≠ 2 := by
        intro h
        apply hmem
        refine Or.inl (Or.inr ?_)
        simp only [Set.mem_singleton_iff]
        congr 1
        exact Subtype.ext h
      have hodd : Odd (p : ℕ) := (p.2.eq_two_or_odd').resolve_left hp2
      have hunr : ∀ w : FinitePlace K, residueChar w = p → ramIdx K w = 1 := by
        intro w hw
        by_contra hne
        apply hmem
        refine Or.inr ⟨w, hne, ?_⟩
        all_goals (simp only [toRational_finite]; congr 1; exact Subtype.ext hw)
      change (LT.packet _ _).productRegion _ = (LT.packet _ _).integralRegion
      ext x
      change (∀ c, x c ∈ LT.logShell (.finite p) (LT.tuple (.finite p) c)) ↔
        ∀ c, x c ∈ LT.integral (.finite p) (LT.tuple (.finite p) c)
      refine forall_congr' fun c => ?_
      have htuple : ∀ j w, LT.tuple (.finite p) c j = Place.finite w → ramIdx K w = 1 := by
        intro j w hw
        apply hunr
        have := (c j).2
        rw [show (c j).1 = Place.finite w from hw, toRational_finite] at this
        exact congrArg Subtype.val (RationalPlace.finite.inj this)
      rw [LT.logShell_eq_integral p (LT.tuple (.finite p) c) hodd htuple]
    · exact absurd (Or.inl (Or.inl rfl)) hmem
  integral_subset_logShell_nonarch i p := by
    intro x hx c
    exact LT.integral_subset_logShell p _ (hx c)

variable (n : ℕ)

@[simp] lemma container_proc : (LT.container n).proc = Procession.standard n := rfl

/-- The packet weight of a tuple: the product of the place weights. -/
noncomputable def tupleWeight {ι : Type} [Fintype ι] (vQ : RationalPlace)
    (c : ι → LT.Fiber vQ) : ℝ :=
  ∏ j, LT.weight vQ (c j)

/-- The scaled integral structure `a·O` of a component. -/
def scaled {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → LT.Fiber vQ)
    (a : LT.Tensor vQ (LT.tuple vQ c)) : Set (LT.Tensor vQ (LT.tuple vQ c)) :=
  a • LT.integral vQ (LT.tuple vQ c)

/-- The element `a·1` of the scaled integral structure `a·O` of a component. -/
def scaledOne {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → LT.Fiber vQ)
    (a : LT.Tensor vQ (LT.tuple vQ c)) : LT.Tensor vQ (LT.tuple vQ c) :=
  a • (1 : LT.Tensor vQ (LT.tuple vQ c))

/-- The projection of a region of the packet to a component. -/
def proj {ι : Type} [Fintype ι] (vQ : RationalPlace) (c : ι → LT.Fiber vQ)
    (U : Set (LT.packet ι vQ).Total) : Set (LT.Tensor vQ (LT.tuple vQ c)) :=
  (fun x => x c) '' U

/-- The projection of a product region with nonempty components is the component. -/
lemma proj_productRegion {ι : Type} [Fintype ι] (vQ : RationalPlace)
    (U : ∀ c : ι → LT.Fiber vQ, Set (LT.Tensor vQ (LT.tuple vQ c)))
    (hU : ∀ c, (U c).Nonempty) (c : ι → LT.Fiber vQ) :
    LT.proj vQ c ((LT.packet ι vQ).productRegion U) = U c := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx c
  · intro hy
    classical
    let choosePoint (c' : ι → LT.Fiber vQ) : LT.Tensor vQ (LT.tuple vQ c') := (hU c').some
    let x := Function.update choosePoint c y
    refine ⟨x, ?_, ?_⟩
    · change ∀ c', Function.update choosePoint c y c' ∈ U c'
      intro c'
      by_cases h : c' = c
      · subst c'
        simpa only [Function.update_self] using hy
      · rw [Function.update_of_ne h]
        exact (hU c').some_mem
    · change Function.update choosePoint c y c = y
      exact Function.update_self c y choosePoint

/-- **The concrete log-volume data** (IUT III, Proposition 3.9). -/
noncomputable def vol : LogVolumeData (LT.container n) where
  weight := LT.weight
  weight_pos := LT.weight_pos
  weight_sum_one := LT.weight_sum_one
  componentVol i vQ c U := LT.componentVol vQ (LT.tuple vQ c) U
  componentVol_integral_nonarch i p c := LT.componentVol_integral _ _
  componentVol_prime_preimage i p c := by
    intro a ha
    exact LT.componentVol_prime_preimage p _ (LT.tuple_isOver p c) _
      (LT.smul_integral_admissible _ _ a ha)
  archBall i c := LT.integral .infinite (LT.tuple .infinite c)
  componentVol_archBall i c := LT.componentVol_integral _ _
  packetVol i vQ U := ∑ c : (LT.container n).Components i vQ,
    LT.tupleWeight vQ c * LT.componentVol vQ (LT.tuple vQ c) (LT.proj vQ c U)
  packetVol_integral i vQ := by
    refine Finset.sum_eq_zero fun c _ => ?_
    have h : LT.proj vQ c ((LT.container n).packet i vQ).integralRegion =
        LT.integral vQ (LT.tuple vQ c) :=
      LT.proj_productRegion vQ (fun c => LT.integral vQ (LT.tuple vQ c))
        (fun c => ⟨1, LT.one_mem_integral vQ _⟩) c
    have := congrArg (fun S => LT.tupleWeight vQ c * LT.componentVol vQ (LT.tuple vQ c) S) h
    rw [LT.componentVol_integral, mul_zero] at this
    exact this
  packetVol_product i vQ U hU := by
    refine Finset.sum_congr rfl fun c _ => ?_
    have h := LT.proj_productRegion vQ U hU c
    exact congrArg (fun S => LT.tupleWeight vQ c * LT.componentVol vQ (LT.tuple vQ c) S) h

/-- **The class of hull regions of a packet** among which the holomorphic hull is least
(`HullSystem.HullRegions`): at a prime all regions `a·O` with all components of `a` units
(IUT III, Remark 3.9.5(i)); at the archimedean place the real radial scalings `t·B_I`
with `t > 0` componentwise (IUT IV, Proposition 1.5(iii)). -/
def hullRegions (ι : Type) [Fintype ι] :
    ∀ vQ : RationalPlace, Set (Set (LT.packet ι vQ).Total)
  | .finite p => {R | (LT.packet ι (.finite p)).IsHullRegion R}
  | .infinite => {R | ∃ t : (ι → LT.Fiber .infinite) → ℝ, (∀ c, 0 < t c) ∧
      R = (LT.packet ι .infinite).scaledIntegral fun c =>
        algebraMap ℝ (LT.Tensor .infinite (LT.tuple .infinite c)) (t c)}

/-- Members of the class of hull regions are hull regions `a·O` with all components of
`a` units. -/
lemma isHullRegion_of_mem_hullRegions (ι : Type) [Fintype ι] (vQ : RationalPlace) :
    ∀ R ∈ LT.hullRegions ι vQ, (LT.packet ι vQ).IsHullRegion R := by
  cases vQ with
  | finite p => exact fun R hR => hR
  | infinite =>
    rintro R ⟨t, ht, rfl⟩
    exact ⟨_, fun c => (isUnit_iff_ne_zero.mpr (ht c).ne').map
      (algebraMap ℝ (LT.Tensor .infinite (LT.tuple .infinite c))), rfl⟩

/-- The holomorphic integral region belongs to the class of hull regions. -/
lemma integralRegion_mem_hullRegions (ι : Type) [Fintype ι] (vQ : RationalPlace) :
    (LT.packet ι vQ).integralRegion ∈ LT.hullRegions ι vQ := by
  cases vQ with
  | finite p => exact (LT.packet ι (.finite p)).isHullRegion_integralRegion
  | infinite =>
    refine ⟨fun _ => 1, fun _ => one_pos, ?_⟩
    rw [← DirectSumPresentation.scaledIntegral_one]
    congr 1
    funext c
    exact (map_one _).symm

/-- **Least hull regions of product regions** with admissible components, from the least
hull regions of the components (`exists_leastHull` at a prime, `exists_leastHull_infinite`
and the radial monotonicity `smul_integral_infinite_mono` at `∞`). -/
lemma exists_leastHullRegion (ι : Type) [Fintype ι] (vQ : RationalPlace)
    (fam : ∀ c : ι → LT.Fiber vQ, Set (LT.Tensor vQ (LT.tuple vQ c)))
    (hfam : ∀ c, fam c ∈ LT.admissible vQ (LT.tuple vQ c)) :
    ∃ R, (LT.packet ι vQ).IsLeastHullRegionIn (LT.hullRegions ι vQ)
      ((LT.packet ι vQ).productRegion fam) R := by
  cases vQ with
  | finite p =>
    choose a ha using fun c => LT.exists_leastHull p (LT.tuple _ c) (fam c) (hfam c)
    refine ⟨(LT.packet _ _).scaledIntegral a, ⟨a, fun c => (ha c).1, rfl⟩, ?_, ?_⟩
    · intro x hx c
      exact (ha c).2.1 (hx c)
    · rintro R ⟨b, hb, rfl⟩ hUR
      intro x hx c
      have hproj : fam c ⊆ LT.scaled _ c (b c) := by
        have := LT.proj_productRegion _ fam
          (fun c => LT.admissible_nonempty _ _ _ (hfam c)) c
        rw [← this]
        rintro y ⟨z, hz, rfl⟩
        exact hUR hz c
      exact (ha c).2.2 (b c) (hb c) hproj (hx c)
  | infinite =>
    choose t ht using fun c => LT.exists_leastHull_infinite (LT.tuple _ c) (fam c) (hfam c)
    refine ⟨(LT.packet _ _).scaledIntegral fun c =>
      algebraMap ℝ (LT.Tensor .infinite (LT.tuple .infinite c)) (t c),
      ⟨t, fun c => (ht c).1, rfl⟩, ?_, ?_⟩
    · intro x hx c
      exact (ht c).2.1 (hx c)
    · rintro R ⟨t', ht', rfl⟩ hUR
      intro x hx c
      have hproj : fam c ⊆ algebraMap ℝ (LT.Tensor .infinite (LT.tuple .infinite c)) (t' c) •
          LT.integral .infinite (LT.tuple .infinite c) := by
        have := LT.proj_productRegion _ fam
          (fun c => LT.admissible_nonempty _ _ _ (hfam c)) c
        rw [← this]
        rintro y ⟨z, hz, rfl⟩
        exact hUR hz c
      exact LT.smul_integral_infinite_mono _ _ _ (ht c).1
        ((ht c).2.2 (t' c) (ht' c) hproj) (hx c)

/-- **The concrete hull system**: least hull regions of product regions with admissible
components, from the least hull regions of the components. -/
noncomputable def hull : ContainerHullSystem (LT.container n) where
  system i vQ :=
    hullSystemOfExists (LT.packet _ vQ)
      {U | ∃ fam : ∀ c, Set (LT.Tensor vQ (LT.tuple vQ c)),
        (∀ c, fam c ∈ LT.admissible vQ (LT.tuple vQ c)) ∧
          U = (LT.packet _ vQ).productRegion fam}
      (by
        rintro U ⟨fam, hfam, rfl⟩
        exact isCompact_closure_productRegion _ _ fun c =>
          LT.admissible_relCompact vQ _ _ (hfam c))
      (LT.hullRegions _ vQ)
      (LT.isHullRegion_of_mem_hullRegions _ vQ)
      (LT.integralRegion_mem_hullRegions _ vQ)
      (by
        rintro U ⟨fam, hfam, rfl⟩
        exact LT.exists_leastHullRegion _ vQ fam hfam)
      (by
        rintro U ⟨fam, hfam, rfl⟩ R ⟨hR, _, _⟩
        obtain ⟨a, ha, rfl⟩ := LT.isHullRegion_of_mem_hullRegions _ vQ R hR
        exact ⟨fun c => LT.scaled vQ c (a c),
          fun c => LT.smul_integral_admissible vQ _ (a c) (ha c), rfl⟩)
  integral_admissible i vQ :=
    ⟨fun c => LT.integral vQ (LT.tuple vQ c), fun c => LT.integral_admissible vQ _, rfl⟩

end LocalTheory

end AbcAdaptation.Reference.Iut
