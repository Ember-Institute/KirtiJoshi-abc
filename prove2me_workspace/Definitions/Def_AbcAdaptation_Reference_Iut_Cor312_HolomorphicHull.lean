/-
Adaptation provenance: this block was inserted by the adaptation; it is not an original source notice.
Original source path: Iut/Cor312/HolomorphicHull.lean
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
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Data.Set.Defs
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.RelClasses
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_PacketPresentation

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference

/-!
# The holomorphic hull on a direct-sum-of-fields presentation (taxis #45)

Following IUT III, Remark 3.9.5, the **holomorphic hull** of a region `U` of a
tensor-packet — presented as a direct sum of fields with holomorphic integral structure
`O` (`Iut.DirectSumPresentation`) — is the smallest region of the form `a · O`
containing `U`, where every direct-summand component of `a` is nonzero
(`Iut.DirectSumPresentation.IsHullRegion`).

## Design and honesty boundary

Whether a least hull region containing `U` *exists* is a genuine theorem of
nonarchimedean/archimedean local-field theory (discreteness of the value group, and the
relative-compactness and finite-log-volume hypotheses of IUT III, Remark 3.9.5(i)); its
proof belongs to the local-field infrastructure tracked in taxis #4 and is **not**
assumed silently here. Instead:

* `IsLeastHullRegionIn 𝓗` states what it means for a region to be *the* hull of `U`
  relative to a class `𝓗` of hull regions (`IsLeastHullRegion` is the case of all hull
  regions `a · O`);
* `HullSystem` packages, as explicit structure fields, a class `Admissible` of regions
  and a class `HullRegions` of hull regions `a · O` containing the integral region,
  together with a hull operation and its defining least-hull-region properties relative
  to `HullRegions`, plus the explicit relative-compactness requirement on admissible
  regions. The class `HullRegions` is part of the data because the hull regions among
  which a least one exists depend on the place: at a nonarchimedean place they are all
  regions `a · O` with `a` a unit; at the archimedean place they are the real radial
  scalings `t · B_I` of the product of unit balls (IUT IV, Proposition 1.5(iii)), among
  arbitrary units a least region need not exist. Producing a `HullSystem` for the
  concrete packets is the certificate discharged by the local-field project (taxis #4);
  nothing in this repository asserts that such a system exists.

Given a `HullSystem`, the four defining elementary properties requested by taxis #45
are **proved** below, not postulated:

1. hull regions are fixed points (`HullSystem.hull_eq_self`);
2. extensivity `U ⊆ hull U` (`HullSystem.subset_hull`);
3. monotonicity (`HullSystem.hull_mono`);
4. the intersection characterization (`HullSystem.hull_eq_sInter`), over the class
   `HullRegions`.

Idempotency (`HullSystem.hull_idem`) follows, and the hull is exposed as a genuine
`ClosureOperator` on the class of admissible regions (`HullSystem.closureOperator`).

**Convention for non-relatively-compact regions.** Admissible regions are required to be
relatively compact (`HullSystem.relCompact_of_admissible`); the hull operation is a total
function on regions, but outside the admissible class its values carry no meaning and no
properties are recorded for them. This is the convention requested by taxis #45
("specify separately the convention for non-relatively-compact regions"): such regions
are simply outside the domain of the recorded interface, rather than being assigned an
ad-hoc improper hull.

## Source correspondence

* Definition of the hull as the least `a · O ⊇ U` with all components of `a` nonzero:
  IUT III, Remark 3.9.5(i).
* Relative-compactness and finite-log-volume hypotheses: IUT III, Remark 3.9.5(i)–(ii).
  The finite-log-volume hypothesis is expressed at the point where a `HullSystem` is
  constructed from log-volume data, since the hull module deliberately does not depend
  on the log-volume module (taxis #44).
-/

namespace Iut

universe u v

namespace DirectSumPresentation

variable {C : Type u} {P : DirectSumPresentation.{u, v} C}

/-- `R` is *the* holomorphic hull of `U` relative to a class `𝓗` of hull regions: a
member of `𝓗` containing `U` and least among the members of `𝓗` containing `U`
(IUT III, Remark 3.9.5(i)). -/
def IsLeastHullRegionIn (P : DirectSumPresentation C) (𝓗 : Set (Set P.Total))
    (U R : Set P.Total) : Prop :=
  R ∈ 𝓗 ∧ U ⊆ R ∧ ∀ R' ∈ 𝓗, U ⊆ R' → R ⊆ R'

end DirectSumPresentation

open DirectSumPresentation

/-- A **hull system** on a direct-sum-of-fields presentation: a class of admissible
regions, required to be relatively compact, on which a holomorphic hull operation with
the defining property of IUT III, Remark 3.9.5(i) is supplied.

This is the interface seam of taxis #45: existence of the least hull region is a
theorem of local-field theory (taxis #4) recorded here as explicit fields, never as
axioms. All four elementary properties of the hull are then *proved* from these fields
(`hull_eq_self`, `subset_hull`, `hull_mono`, `hull_eq_sInter`). -/
structure HullSystem {C : Type u} (P : DirectSumPresentation.{u, v} C) :
    Type (max u v) where
  /-- The class of admissible regions on which the hull operates. In the intended
  instantiation: nonempty relatively compact regions of finite nonzero log-volume with
  nonzero component projections (IUT III, Remark 3.9.5(i)). -/
  Admissible : Set (Set P.Total)
  /-- Explicit hypothesis: admissible regions are relatively compact. Regions that are
  not relatively compact are outside the domain of this interface. -/
  relCompact_of_admissible : ∀ U ∈ Admissible, IsCompact (closure U)
  /-- The class of hull regions among which the hull is least: at a nonarchimedean place
  all regions `a · O` with `a` a unit, at the archimedean place the real radial scalings
  `t · B_I` (IUT IV, Proposition 1.5(iii)). -/
  HullRegions : Set (Set P.Total)
  /-- Members of the class are hull regions `a · O` with all components of `a` units. -/
  isHullRegion_of_mem : ∀ R ∈ HullRegions, P.IsHullRegion R
  /-- The holomorphic integral region belongs to the class. -/
  integralRegion_mem : P.integralRegion ∈ HullRegions
  /-- The holomorphic hull operation. Values outside `Admissible` are junk. -/
  hull : Set P.Total → Set P.Total
  /-- The hull of an admissible region is the least member of `HullRegions` containing it
  (IUT III, Remark 3.9.5(i)). -/
  isLeastHullRegion_hull : ∀ U ∈ Admissible, P.IsLeastHullRegionIn HullRegions U (hull U)
  /-- The admissible class is stable under the hull operation, so that the hull is a
  closure operator on admissible regions. -/
  hull_admissible : ∀ U ∈ Admissible, hull U ∈ Admissible

namespace HullSystem

variable {C : Type u} {P : DirectSumPresentation.{u, v} C} (H : HullSystem P)

variable {U V : Set P.Total}

/-- **Extensivity** (taxis #45, property 2): `U` is contained in its holomorphic hull. -/
lemma subset_hull (hU : U ∈ H.Admissible) : U ⊆ H.hull U :=
  (H.isLeastHullRegion_hull U hU).2.1

/-- Minimality: the hull of `U` is contained in every member of the class of hull
regions containing `U`. -/
lemma hull_le (hU : U ∈ H.Admissible) {R : Set P.Total}
    (hR : R ∈ H.HullRegions) (hUR : U ⊆ R) : H.hull U ⊆ R :=
  (H.isLeastHullRegion_hull U hU).2.2 R hR hUR

/-- **Hull regions are fixed points** (taxis #45, property 1): if an admissible region
is itself a member of the class of hull regions, it is its own hull. -/
theorem hull_eq_self (hU : U ∈ H.Admissible) (h : U ∈ H.HullRegions) : H.hull U = U :=
  Set.Subset.antisymm (H.hull_le hU h subset_rfl) (H.subset_hull hU)

end HullSystem

end Iut

end AbcAdaptation.Reference
