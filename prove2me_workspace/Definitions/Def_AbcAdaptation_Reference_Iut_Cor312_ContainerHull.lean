/-
Adaptation provenance: this block was inserted by the adaptation; it is not an original source notice.
Original source path: Iut/Cor312/ContainerHull.lean
Original authors: The iut contributors
Original repository: https://github.com/lana-agents/iut
Original commit: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original license: Apache-2.0; the original copyright and license notice is retained below.
-/
/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_Container
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_HolomorphicHull
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_PacketPresentation
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_Procession
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_RationalPlace

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference

/-!
# The holomorphic hull on the large volume container (taxis #45)

Extension of the local holomorphic hull (`Iut.HullSystem`, IUT III, Remark 3.9.5) across
the structure of the large volume container of taxis #43:

* across the `v_Q`-indexed local tensor-packets: a `ContainerHullSystem` supplies one
  hull system per capsule index and rational place, so the packet and place indexing is
  preserved rather than replaced by a coordinate-free enlargement;
* across capsules and their procession labels: the hull of a family of admissible
  regions indexed by the capsules is taken capsule-by-capsule
  (`ContainerHullSystem.hullFamily`), retaining the labels;
* across the global/restricted-product container: the hull of an admissible region of
  the container is again an admissible region (`ContainerHullSystem.hullAdmissible`) —
  the finite-support condition is *proved* to be preserved, using that the holomorphic
  integral region is its own hull.

The local hull `a·O` (IUT III, Remark 3.9.5(i)) is literally defined at the local level;
the global extension here differs from the local definition only in that it is applied
placewise and capsule-wise, which is documented as required by taxis #45. All
compactness, nonzero-component and existence hypotheses remain explicit: they are the
fields of the local `HullSystem`s, plus the admissibility hypotheses `adm` of the
definitions below. No log-volume inequality is built in, and nothing asserts that a
theta-pilot output lies in any hull (out of scope for taxis #45).
-/

namespace Iut

universe u₁ u₂ v

variable {ι : Type u₁} {V : Type u₂}

open LargeVolumeContainerData

/-- A family of holomorphic hull systems for every packet of a large volume container,
together with the requirement that each holomorphic integral region is admissible for
its hull system. This is the datum through which the local hull of IUT III,
Remark 3.9.5 is extended across the `v_Q`-indexed packets of the container. -/
structure ContainerHullSystem (D : LargeVolumeContainerData.{u₁, u₂, v} ι V) :
    Type (max u₁ u₂ v) where
  /-- The hull system of the packet at capsule `i` and rational place `v_Q`. -/
  system : ∀ (i : Fin D.proc.length) (vQ : RationalPlace), HullSystem (D.packet i vQ)
  /-- The holomorphic integral region of each packet is admissible. Together with
  `Iut.HullSystem.integralRegion_mem` this makes the integral region its own hull, so
  hulls preserve the finite-support condition of the container's admissible regions. -/
  integral_admissible :
    ∀ i vQ, (D.packet i vQ).integralRegion ∈ (system i vQ).Admissible

namespace ContainerHullSystem

variable {D : LargeVolumeContainerData.{u₁, u₂, v} ι V} (H : ContainerHullSystem D)

variable {i : Fin D.proc.length}

/-- An admissible region of the container is hull-admissible if each of its packet
regions is admissible for the packet's hull system. -/
def IsAdmissible (R : D.AdmissibleRegion i) : Prop :=
  ∀ vQ, R.region vQ ∈ (H.system i vQ).Admissible

/-- The holomorphic integral region is its own hull. -/
lemma hull_integralRegion (vQ : RationalPlace) :
    (H.system i vQ).hull (D.packet i vQ).integralRegion =
      (D.packet i vQ).integralRegion :=
  (H.system i vQ).hull_eq_self (H.integral_admissible i vQ) (H.system i vQ).integralRegion_mem

/-- The **holomorphic hull of an admissible region of the container**: the packet-wise
hull. The finite-support condition is preserved because the holomorphic integral
region is its own hull; the `v_Q`-indexing and the capsule index are retained. -/
def hullAdmissible (R : D.AdmissibleRegion i) : D.AdmissibleRegion i where
  region vQ := (H.system i vQ).hull (R.region vQ)
  finiteSupport := by
    refine R.finiteSupport.subset fun vQ hvQ h => ?_
    apply hvQ
    rw [h]
    exact H.hull_integralRegion vQ

/-- The **capsule-indexed hull**: the holomorphic hull of a family of admissible
regions indexed by the capsules of the procession, taken capsule-by-capsule. The
procession labels are retained: the result is again a capsule-indexed family. -/
def hullFamily (R : ∀ i : Fin D.proc.length, D.AdmissibleRegion i) :
    ∀ i : Fin D.proc.length, D.AdmissibleRegion i :=
  fun i => H.hullAdmissible (R i)

end ContainerHullSystem

end Iut

end AbcAdaptation.Reference
