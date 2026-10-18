/-
original-paths: refer/iut/Iut/Concrete/Container.lean,
  refer/iut/Iut/Cor312/Container.lean
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commits: Concrete/Container be25c6c14681a180795dc60972941472ce4d2645,
  Cor312/Container 0702e371fa9ecf639fb469038281dced22907723
source-snapshot: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
license: Apache-2.0 (see project LICENSE)
modification: adapt place-fiber equivalences and restricted-product shape
  to already proved actual finite and infinite packet regions. No reference
  LocalTheory, container contract, or theta-pilot input is imported.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.Scene1RationalPlace
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePacketRegion
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFinitePacketLogVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaArchimedeanPacketRegion
import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
source-id: JT-SCENE1-INITIAL-THETA-ADELIC-PACKET-REGION
source: reference Concrete/Container and Cor312/Container for rational-place
fibers and the restricted product; Concrete/ThetaRegion, thetaPilot, for
finite support. Joshi III th:thetam-construction is the intended adelic target.
fidelity: unifies actual finite and infinite packet regions from the same D.
Proves place-fiber/tuple equivalences, compactness, positive finite local
product measure, and a common finite exceptional set for every capsule.
The actual nonempty region is formed in the restricted product relative to
the integral regions. No infinite product measure or paper theta identity
is asserted. All additional proofs are original consumers.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.IutInitialThetaAdelicPacketRegion

open NumberField MeasureTheory
open scoped BigOperators Classical RestrictedProduct

universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

private abbrev K := ↥D.prime.torsionField

def toRational : JoshiTeich.ReferenceIut.Place (K D) → RationalPlace
  | Sum.inl w => .finite ⟨JoshiTeich.Prologue.Arithmetic.residueChar w,
      JoshiTeich.Prologue.Arithmetic.residueChar_prime w⟩
  | Sum.inr _ => .infinite

abbrev PlaceFiber (vQ : RationalPlace) :=
  {v : JoshiTeich.ReferenceIut.Place (K D) // toRational D v = vQ}

def fiberFiniteEquiv (p : Nat.Primes) :
    PlaceFiber D (.finite p) ≃ IutInitialThetaFinitePacketRegion.Fiber D p where
  toFun v := match v with
    | ⟨Sum.inl w, h⟩ => ⟨w, congrArg Subtype.val (RationalPlace.finite.inj h)⟩
    | ⟨Sum.inr _, h⟩ => absurd h (by simp [toRational])
  invFun w := ⟨Sum.inl w.1, by
    change RationalPlace.finite _ = .finite p
    exact congrArg RationalPlace.finite (Subtype.ext w.2)⟩
  left_inv v := by
    rcases v with ⟨v, h⟩
    rcases v with w | w
    · rfl
    · exact absurd h (by simp [toRational])
  right_inv _ := rfl

def fiberInfiniteEquiv : PlaceFiber D .infinite ≃ InfinitePlace (K D) where
  toFun v := match v with
    | ⟨Sum.inl _, h⟩ => absurd h (by simp [toRational])
    | ⟨Sum.inr w, _⟩ => w
  invFun w := ⟨Sum.inr w, rfl⟩
  left_inv v := by
    rcases v with ⟨v, h⟩
    rcases v with w | w
    · exact absurd h (by simp [toRational])
    · rfl
  right_inv _ := rfl

def Tuple (j : ℕ) : RationalPlace → Type u
  | .finite p => IutInitialThetaFinitePacketRegion.Tuple D p j
  | .infinite => IutInitialThetaArchimedeanPacketRegion.Tuple D j

def placeTupleEquiv (j : ℕ) (vQ : RationalPlace) :
    (Fin (j + 1) → PlaceFiber D vQ) ≃ Tuple D j vQ := by
  cases vQ with
  | finite p => exact Equiv.piCongrRight (fun _ => fiberFiniteEquiv D p)
  | infinite => exact Equiv.piCongrRight (fun _ => fiberInfiniteEquiv D)

def Total (j : ℕ) : RationalPlace → Type u
  | .finite p => IutInitialThetaFinitePacketRegion.Total D p j
  | .infinite => IutInitialThetaArchimedeanPacketRegion.Total D j

instance totalTopologicalSpace (j : ℕ) (vQ : RationalPlace) : TopologicalSpace (Total D j vQ) :=
  match vQ with
  | .finite p => inferInstanceAs (TopologicalSpace (IutInitialThetaFinitePacketRegion.Total D p j))
  | .infinite => inferInstanceAs (TopologicalSpace (IutInitialThetaArchimedeanPacketRegion.Total D j))

instance totalMeasurableSpace (j : ℕ) (vQ : RationalPlace) : MeasurableSpace (Total D j vQ) :=
  match vQ with
  | .finite p => inferInstanceAs (MeasurableSpace (IutInitialThetaFinitePacketRegion.Total D p j))
  | .infinite => inferInstanceAs (MeasurableSpace (IutInitialThetaArchimedeanPacketRegion.Total D j))

def region (j : ℕ) : (vQ : RationalPlace) → Set (Total D j vQ)
  | .finite p => IutInitialThetaFinitePacketRegion.region D p j
  | .infinite => IutInitialThetaArchimedeanPacketRegion.region D j

def integralRegion (j : ℕ) : (vQ : RationalPlace) → Set (Total D j vQ)
  | .finite p => IutInitialThetaFinitePacketRegion.integralRegion D p j
  | .infinite => IutInitialThetaArchimedeanPacketRegion.integralRegion D j

def packetMeasure (j : ℕ) : (vQ : RationalPlace) → Measure (Total D j vQ)
  | .finite p => IutInitialThetaFinitePacketRegion.productMeasure D p j
  | .infinite => IutInitialThetaArchimedeanPacketRegion.productMeasure D j

theorem region_isCompact (j : ℕ) (vQ : RationalPlace) : IsCompact (region D j vQ) := by
  cases vQ with
  | finite p => exact IutInitialThetaFinitePacketRegion.region_isCompact D p j
  | infinite => exact IutInitialThetaArchimedeanPacketRegion.region_isCompact D j

theorem packetMeasure_integralRegion (j : ℕ) (vQ : RationalPlace) :
    packetMeasure D j vQ (integralRegion D j vQ) = 1 := by
  cases vQ with
  | finite p => exact IutInitialThetaFinitePacketRegion.productMeasure_integralRegion D p j
  | infinite => exact IutInitialThetaArchimedeanPacketRegion.productMeasure_integralRegion D j

theorem packetMeasure_region_pos_lt_top (j : ℕ) (vQ : RationalPlace) :
    0 < packetMeasure D j vQ (region D j vQ) ∧
      packetMeasure D j vQ (region D j vQ) < ⊤ := by
  cases vQ with
  | finite p => exact IutInitialThetaFinitePacketRegion.productMeasure_region_pos_lt_top D p j
  | infinite => exact IutInitialThetaArchimedeanPacketRegion.productMeasure_region_pos_lt_top D j

def exceptionalPlaces : Finset RationalPlace :=
  insert .infinite ((IutInitialThetaFinitePacketLogVolume.badPrimes D).image RationalPlace.finite)

theorem finite_mem_exceptionalPlaces (p : Nat.Primes) :
    RationalPlace.finite p ∈ exceptionalPlaces D ↔
      p ∈ IutInitialThetaFinitePacketLogVolume.badPrimes D := by
  simp [exceptionalPlaces]

theorem region_eq_integralRegion_of_not_exceptional (j : ℕ) (vQ : RationalPlace)
    (hv : vQ ∉ exceptionalPlaces D) : region D j vQ = integralRegion D j vQ := by
  cases vQ with
  | finite p =>
    apply IutInitialThetaFinitePacketRegion.region_eq_integralRegion_of_not_bad
    intro hp
    exact hv ((finite_mem_exceptionalPlaces D p).mpr
      ((IutInitialThetaFinitePacketLogVolume.mem_badPrimes D p).mpr hp))
  | infinite => exact False.elim (hv (Finset.mem_insert_self _ _))

theorem region_support_subset (j : ℕ) :
    {vQ | region D j vQ ≠ integralRegion D j vQ} ⊆ (exceptionalPlaces D : Set RationalPlace) := by
  intro vQ hv
  by_contra h
  exact hv (region_eq_integralRegion_of_not_exceptional D j vQ h)

theorem region_finite_support (j : ℕ) :
    {vQ | region D j vQ ≠ integralRegion D j vQ}.Finite :=
  (exceptionalPlaces D).finite_toSet.subset (region_support_subset D j)

theorem processionRegion_finite_support :
    {vQ | ∃ i : IutInitialThetaFinitePacketRegion.Index D,
      region D (i.val + 1) vQ ≠ integralRegion D (i.val + 1) vQ}.Finite := by
  apply (exceptionalPlaces D).finite_toSet.subset
  rintro vQ ⟨i, hi⟩
  exact region_support_subset D (i.val + 1) hi

abbrev Container (j : ℕ) := Πʳ vQ, [Total D j vQ, integralRegion D j vQ]

def containerRegion (j : ℕ) : Set (Container D j) := {x | ∀ vQ, x vQ ∈ region D j vQ}

theorem integral_eventually_of_mem_region (j : ℕ) (x : ∀ vQ, Total D j vQ)
    (hx : ∀ vQ, x vQ ∈ region D j vQ) :
    ∀ᶠ vQ in Filter.cofinite, x vQ ∈ integralRegion D j vQ := by
  filter_upwards [(exceptionalPlaces D).eventually_cofinite_notMem] with vQ hv
  rw [← region_eq_integralRegion_of_not_exceptional D j vQ hv]
  exact hx vQ

def toContainer (j : ℕ) (x : ∀ vQ, Total D j vQ) (hx : ∀ vQ, x vQ ∈ region D j vQ) :
    Container D j := ⟨x, integral_eventually_of_mem_region D j x hx⟩

theorem toContainer_mem (j : ℕ) (x : ∀ vQ, Total D j vQ)
    (hx : ∀ vQ, x vQ ∈ region D j vQ) : toContainer D j x hx ∈ containerRegion D j := hx

theorem region_nonempty (j : ℕ) (vQ : RationalPlace) : (region D j vQ).Nonempty := by
  by_contra h
  have he := Set.not_nonempty_iff_eq_empty.mp h
  have hpos := (packetMeasure_region_pos_lt_top D j vQ).1
  rw [he, measure_empty] at hpos
  exact (lt_irrefl _ hpos)

def witness (j : ℕ) : Container D j :=
  toContainer D j (fun vQ => (region_nonempty D j vQ).choose)
    (fun vQ => (region_nonempty D j vQ).choose_spec)

theorem witness_mem_containerRegion (j : ℕ) : witness D j ∈ containerRegion D j :=
  fun vQ => (region_nonempty D j vQ).choose_spec

theorem containerRegion_nonempty (j : ℕ) : (containerRegion D j).Nonempty :=
  ⟨witness D j, witness_mem_containerRegion D j⟩

end
end JoshiTeich.Act1Scene1.IutInitialThetaAdelicPacketRegion
