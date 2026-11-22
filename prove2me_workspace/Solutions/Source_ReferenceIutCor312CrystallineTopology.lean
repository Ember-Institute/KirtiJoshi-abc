import Solutions.Source_ReferenceIutCor312MappedTatePeriod
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Topology.Algebra.Localization
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open scoped Topology
open Filter

noncomputable section

private theorem sub_mem_adicCompletion_pow_iff_eval_eq
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG) (k : ℕ)
    (w z : AdicCompletion I R) :
    w - z ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ k ↔
      AdicCompletion.evalₐ I k w = AdicCompletion.evalₐ I k z := by
  rw [← Ideal.map_pow]
  change w - z ∈ ((I ^ k).map (algebraMap R (AdicCompletion I R))).restrictScalars R ↔ _
  rw [← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (M := R) (n := k) hI]
  change AdicCompletion.eval I R k (w - z) = 0 ↔ _
  have hpow : (I ^ k • ⊤ : Ideal R) = I ^ k := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  let e := AdicCompletion.evalₐ I k
  constructor
  · intro hw
    have hm := AdicCompletion.factor_eval_eq_evalₐ I (w - z) hpow.le
    rw [hw, map_zero] at hm
    exact sub_eq_zero.mp ((map_sub e w z).symm.trans hm.symm)
  · intro hw
    have he : e (w - z) = 0 := (map_sub e w z).trans (sub_eq_zero.mpr hw)
    have hm := AdicCompletion.factor_evalₐ_eq_eval I (w - z) hpow.ge
    change Ideal.Quotient.factor hpow.ge (e (w - z)) = _ at hm
    rw [he, map_zero] at hm
    exact hm.symm

private theorem sub_mem_primeAdicCompletion_pow_iff_eval_eq
    {R : Type*} [CommRing R] (p k : ℕ)
    (w z : AdicCompletion (Ideal.span {(p : R)}) R) :
    w - z ∈ (Ideal.span {(p : AdicCompletion (Ideal.span {(p : R)}) R)}) ^ k ↔
      AdicCompletion.evalₐ (Ideal.span {(p : R)}) k w =
        AdicCompletion.evalₐ (Ideal.span {(p : R)}) k z := by
  let I : Ideal R := Ideal.span {(p : R)}
  have hMap : I.map (algebraMap R (AdicCompletion I R)) =
      Ideal.span {(p : AdicCompletion I R)} := by
    change (Ideal.span {(p : R)}).map (algebraMap R (AdicCompletion I R)) = _
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hMap]
  exact sub_mem_adicCompletion_pow_iff_eval_eq I (Submodule.fg_span_singleton (p : R)) k w z

private theorem hasBasis_nhds_primeAdicCompletion {R : Type*} [CommRing R] (p : ℕ)
    (z : AdicCompletion (Ideal.span {(p : R)}) R) :
    let A := AdicCompletion (Ideal.span {(p : R)}) R
    let J : Ideal A := Ideal.span {(p : A)}
    (@nhds _ J.adicTopology z).HasBasis (fun _ : ℕ => True)
      (fun k => {w | AdicCompletion.evalₐ (Ideal.span {(p : R)}) k w =
        AdicCompletion.evalₐ (Ideal.span {(p : R)}) k z}) := by
  let A := AdicCompletion (Ideal.span {(p : R)}) R
  let J : Ideal A := Ideal.span {(p : A)}
  refine (J.hasBasis_nhds_adic z).congr (fun _ => Iff.rfl) fun k _ => ?_
  ext w
  let I : Ideal R := Ideal.span {(p : R)}
  change (w ∈ (fun y : A => z + y) '' ↑(J ^ k)) ↔
    AdicCompletion.evalₐ I k w = AdicCompletion.evalₐ I k z
  have hEval := sub_mem_primeAdicCompletion_pow_iff_eval_eq p k w z
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply (sub_mem_primeAdicCompletion_pow_iff_eval_eq p k (z + y) z).mp
    change (z + y) - z ∈ J ^ k
    rwa [add_comm z y, add_sub_cancel_right]
  · intro h
    exact ⟨w - z, hEval.mpr h, (add_comm z (w - z)).trans (sub_add_cancel w z)⟩

/-- The canonical map into a localization is continuous for its final ring topology. -/
theorem continuous_algebraMap_localization {R : Type*} [CommRing R] [TopologicalSpace R]
    (M : Submonoid R) : Continuous (algebraMap R (Localization M)) :=
  RingTopology.coinduced_continuous (Localization.monoidOf M).toFun

private def induced_ringTopology {R S : Type*} [Ring R] [Ring S] [TopologicalSpace S]
    [IsTopologicalRing S] (f : R →+* S) : RingTopology R := by
  letI : TopologicalSpace R := TopologicalSpace.induced f inferInstance
  have h : IsTopologicalSemiring R :=
    { toContinuousAdd := continuousAdd_induced f
      toContinuousMul := continuousMul_induced f }
  exact ⟨inferInstance, h.toIsTopologicalRing⟩

/-- A ring homomorphism out of a localization is continuous when its
composition with the canonical map into the localization is continuous. -/
theorem continuous_of_continuous_comp_localization {R S : Type*} [CommRing R] [Ring S]
    [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing S]
    (M : Submonoid R) (f : Localization M →+* S)
    (hf : Continuous (f.comp (algebraMap R (Localization M)))) : Continuous f := by
  let pullback := induced_ringTopology f
  have h : Continuous[(inferInstance : TopologicalSpace R), pullback.toTopologicalSpace]
      (Localization.monoidOf M).toFun := continuous_induced_rng.mpr hf
  apply continuous_iff_le_induced.mpr
  change (RingTopology.coinduced (Localization.monoidOf M).toFun) ≤ pullback
  exact sInf_le (continuous_iff_coinduced_le.mp h)

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "D" => A0 C p
local notation "A" => ACris C p
local notation "I" => (Ideal.span {(p : D)} : Ideal D)
local notation "J" => (Ideal.span {(p : A)} : Ideal A)
local notation "B" => ACrisInvertP C p

/-- The crystalline completion with the topology of the powers of the prime ideal. -/
scoped instance instTopologicalSpaceACris : TopologicalSpace A := Ideal.adicTopology J

scoped instance instIsTopologicalRingACris : IsTopologicalRing A :=
  (Ideal.nonarchimedean J).toIsTopologicalRing

/-- In the adic topology, the fibers through an element of the prime-power
evaluation maps give a basis of its neighborhoods. -/
theorem hasBasis_nhds_ACris_evalₐ (z : A) :
    (𝓝 z).HasBasis (fun _ : ℕ => True)
      (fun k => {w : A | AdicCompletion.evalₐ I k w = AdicCompletion.evalₐ I k z}) :=
  hasBasis_nhds_primeAdicCompletion p z

/-- Continuity into the crystalline completion is equivalent to eventual
equality in each prime-power evaluation at each source point. -/
theorem continuous_into_ACris_iff_eventually_evalₐ_eq {X : Type*} [TopologicalSpace X]
    (f : X → A) :
    Continuous f ↔ ∀ (x : X) (k : ℕ), ∀ᶠ y in 𝓝 x,
      AdicCompletion.evalₐ I k (f y) = AdicCompletion.evalₐ I k (f x) := by
  constructor
  · intro hf x k
    exact (hasBasis_nhds_ACris_evalₐ C p (f x)).tendsto_right_iff.mp hf.continuousAt k trivial
  · intro h
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hasBasis_nhds_ACris_evalₐ C p (f x)).tendsto_right_iff.mpr fun k _ => h x k

theorem continuous_algebraMap_ACrisInvertP :
    Continuous (algebraMap A B) :=
  continuous_algebraMap_localization (Submonoid.powers (p : A))

variable {Ω : Type*} [Field Ω] [CharZero Ω] [IsAlgClosed Ω]
variable (j : Ω →+* C)

local notation "Bₜ" => ACrisInvertTatePeriod C p j

theorem continuous_algebraMap_ACrisInvertTatePeriod :
    Continuous (algebraMap B Bₜ) :=
  continuous_algebraMap_localization (Submonoid.powers (mappedTateBasisPeriod C p j))

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
