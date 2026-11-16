/-
Adaptation provenance: this block was inserted by the adaptation; it is not an original source notice.
Original source path: Iut/Cor312/ThetaData/LocalConditions.lean
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
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.WithAbs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Category.CompHausLike.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_AdmissiblePrime
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Orbicurve
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Places

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference

/-!
# Initial Θ-data: valuation section and local conditions (taxis #42)

The valuation-indexed local portion of initial Θ-data, IUT I, Definition 3.1(e) and the
local part of (f), for the Corollary 3.12 variant statement (taxis #33).

## Contents

* The `ℓ`-torsion field `K` is finite over `F` — **proved** from openness of the kernel
  of the mod-`ℓ` representation (`AdmissiblePrimeData.finiteDimensional_torsionField`),
  giving `K` its `NumberField` instance.
* `Iut.ValuationSection`: a section `V ⊆ V(K)` of the restriction `V(K) → V_mod`,
  given by place-type-preserving maps on finite and infinite places, each lying over
  its base point; with the derived subsets `V^non`, `V^arc`, `V^good`, `V^bad`.
* `Iut.TemperedGeometry`: the interface extension supplying tempered fundamental
  groups over complete nonarchimedean fields, their comparison maps to the profinite
  étale fundamental groups, the theta-root model predicate, and the canonical
  graph-quotient cusp (seams for taxis #7 `lana-agents/tempered-fundamental-groups`,
  taxis #11 `lana-agents/continuous-kummer-theory`, and taxis #13
  `lana-agents/tate-curves-theta`, as directed by taxis #42).
* `Iut.LocalThetaData`: the packaged local data and conditions: completions and base
  changes at `v ∈ V`, the cartesian local covering diagrams with their injections of
  fundamental groups (available from `AnabelianGeometry.pi1Cover` and its open
  embedding property), decomposition groups up to conjugacy, the type `(1, ℤ/ℓℤ)^±`
  and theta-root-model conditions at bad places, the cusp condition for `ε_v`, and the
  `Π_v` convention (tempered at bad places, étale at good places).

## Honesty boundary

Tempered fundamental groups, theta-root models, and graph-quotient cusps are interface
fields, discharged by the anabelian projects listed above; conditions are structure
fields, never axioms. This module states the local conditions and interfaces; it does
not prove that arbitrary global elliptic curves satisfy them (out of scope for
taxis #42).

## Source correspondence

IUT I, Definition 3.1(e)–(f), pp. 70–71, including the local covering diagrams;
*The Étale Theta Function*, Definition 2.5 (the natural models obtained by extracting
an `ℓ`-th root of the theta function, and the cusp attached to the canonical generator
`±1` of the graph quotient).
-/

namespace Iut

universe u

open NumberField IsDedekindDomain WeierstrassCurve OrbicurveDataSection

/-! ## Finiteness of the ℓ-torsion field -/

section TorsionFieldFinite

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]

variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]

variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

end TorsionFieldFinite

/-! ## The tempered interface -/

/-- Interface extension for the local anabelian geometry at nonarchimedean places
(seams for taxis #7, #11, #13): tempered fundamental groups with their comparison to
the profinite étale fundamental groups, the theta-root model predicate of *The Étale
Theta Function*, Definition 2.5, and the canonical graph-quotient cusp. -/
structure TemperedGeometry (AG : AnabelianGeometry.{u}) : Type (u + 1) where
  /-- The tempered fundamental group of an orbicurve over a (complete nonarchimedean)
  field. Unlike the étale fundamental group it is not profinite; it is carried as a
  bare type with group and topology instances supplied by the fields below. -/
  tempPi1 : {k : Type u} → [Field k] → AG.Orbicurve k → Type u
  /-- Group structure on the tempered fundamental group. -/
  tempPi1Group : ∀ {k : Type u} [Field k] (X : AG.Orbicurve k), Group (tempPi1 X)
  /-- Topology on the tempered fundamental group. -/
  tempPi1Topology : ∀ {k : Type u} [Field k] (X : AG.Orbicurve k),
    TopologicalSpace (tempPi1 X)
  /-- The comparison homomorphism from the tempered fundamental group to the
  profinite étale fundamental group (its profinite completion). -/
  tempToEtale : ∀ {k : Type u} [Field k] (X : AG.Orbicurve k),
    letI := tempPi1Group X; tempPi1 X →* AG.pi1 X
  /-- The comparison homomorphism is continuous. -/
  tempToEtale_continuous : ∀ {k : Type u} [Field k] (X : AG.Orbicurve k),
    letI := tempPi1Group X; letI := tempPi1Topology X
    Continuous (tempToEtale X)
  /-- The orbicurve is a **natural model obtained by extracting an `ℓ`-th root of the
  theta function** (*The Étale Theta Function*, Definition 2.5). The precise content
  of this predicate is supplied by the étale-theta continuation of taxis #13; here it
  is an interface predicate consumed by the bad-place conditions. -/
  IsThetaRootModel : {k : Type u} → [Field k] → [Valued k (WithZero (Multiplicative ℤ))] →
    [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] → [CompleteSpace k] →
    (ℓ : ℕ) → (X : AG.Orbicurve k) → AG.TateStructure X → Prop
  /-- The cusp associated to the **canonical generator `±1` of the graph quotient** of
  an orbicurve over a complete nonarchimedean field with stable multiplicative-type
  reduction (*The Étale Theta Function*, Definition 2.5; junk value outside that
  regime), relative to a Tate structure on the orbicurve. -/
  canonicalGraphCusp : {k : Type u} → [Field k] → [Valued k (WithZero (Multiplicative ℤ))] →
    [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] → [CompleteSpace k] →
    (X : AG.Orbicurve k) → AG.TateStructure X → AG.Cusp X

/-! ## The valuation section and local data -/

section LocalData

variable (AG : AnabelianGeometry.{u}) (TG : TemperedGeometry AG)

variable (F : Type u) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]

variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar]

variable (VBad : Set (FinitePlace ↥(fieldOfModuli F E)))

variable (P : AdmissiblePrimeData F E Fbar VBad)

variable [NumberField ↥P.torsionField]

variable [Algebra ↥(fieldOfModuli F E) ↥P.torsionField]

/-- A **section** `V ⊆ V(K)` of the restriction map `V(K) → V_mod`
(IUT I, Definition 3.1(e)): a choice, for every place of `F_mod`, of a place of `K` of
the same type (nonarchimedean/archimedean) lying over it. The subset `V ⊆ V(K)` is the
image of the section; `V ≅ V_mod`. The `NumberField` instance on `K` is available via
`AdmissiblePrimeData.numberField_torsionField`, and the algebra `F_mod → K` (the
restriction of the inclusions into `F̄`) is carried as an instance hypothesis. -/
structure ValuationSection : Type u where
  /-- The section on nonarchimedean places. -/
  sectFin : FinitePlace ↥(fieldOfModuli F E) → FinitePlace ↥P.torsionField
  /-- The section on archimedean places. -/
  sectInf : InfinitePlace ↥(fieldOfModuli F E) → InfinitePlace ↥P.torsionField
  /-- Nonarchimedean sections lie over their base points. -/
  sectFin_liesOver : ∀ v, FinitePlace.LiesOver (sectFin v) v
  /-- Archimedean sections lie over their base points. -/
  sectInf_liesOver : ∀ v, (sectInf v).1.LiesOver v.1

namespace ValuationSection

variable {AG TG F E Fbar VBad P}

variable (S : ValuationSection F E Fbar VBad P)

end ValuationSection

variable {AG TG F E Fbar VBad P} in
/-- The base change of an orbicurve over `K` to the completed local field `K_v` at a
finite place `v` of `K`. -/
noncomputable def localize (v : FinitePlace ↥P.torsionField)
    (X : AG.Orbicurve ↥P.torsionField) : AG.Orbicurve (localCompletion v) :=
  AG.baseChange (FinitePlace.embedding v.maximalIdeal) X

/-- **IUT I, Definition 3.1(e) and the local part of (f)**: the valuation section with
its local completions, covering diagrams, decomposition groups, and the bad-place
conditions, packaged over the orbicurve data of taxis #41. -/
structure LocalThetaData (O : OrbicurveData AG F E Fbar VBad P) : Type u where
  /-- The valuation section `V ⊆ V(K)`. -/
  sect : ValuationSection F E Fbar VBad P
  /-- The cartesian local covering diagrams (IUT I, Definition 3.1(e)): at every
  finite place `v` of the section, the base change to `K_v` of the global diagram
  remains cartesian. The injections (open immersions) of local fundamental groups are
  `AG.pi1Cover` of the base-changed covers, with `AG.pi1Cover_isOpenEmbedding`. -/
  local_diagram_cartesian : ∀ v : FinitePlace ↥(fieldOfModuli F E),
    AG.IsCartesianSquare
      (AG.coverBaseChange (FinitePlace.embedding (sect.sectFin v).maximalIdeal)
        O.XKu_to_XK)
      (AG.coverBaseChange (FinitePlace.embedding (sect.sectFin v).maximalIdeal)
        O.XK_to_CK)
      (AG.coverBaseChange (FinitePlace.embedding (sect.sectFin v).maximalIdeal)
        O.XKu_to_CKu)
      (AG.coverBaseChange (FinitePlace.embedding (sect.sectFin v).maximalIdeal)
        O.CKu_to_CK)
  /-- A choice of **decomposition group** `G_v ⊆ Gal(F̄/K)` at every finite place of
  the section (IUT I, Definition 3.1(e); the group is well-defined up to conjugacy,
  and this field is a choice of representative). -/
  decomp : ∀ _ : FinitePlace ↥P.torsionField, Subgroup (Fbar ≃ₐ[↥P.torsionField] Fbar)
  /-- Decomposition groups are closed in the Krull topology. -/
  decomp_isClosed : ∀ v, IsClosed ((decomp v) : Set (Fbar ≃ₐ[↥P.torsionField] Fbar))
  /-- The Tate structure (Tate uniformization of `E` over `K_v`) on the local model `X̲_v`
  at each place of the section over `V_mod^bad` (IUT I, Definition 3.1(f) refers to the
  Tate uniformization; chosen data, pinned by the coordinates of the Tate parametrization
  in `Iut.TateStructure`). -/
  tateX : ∀ v ∈ VBad, AG.TateStructure (localize (sect.sectFin v) O.XKu)
  /-- The Tate structure on the local model `C̲_v`. -/
  tateC : ∀ v ∈ VBad, AG.TateStructure (localize (sect.sectFin v) O.CKu)
  /-- At places over `V_mod^bad`, the local model `X̲_v = X̲_K ×_K K_v` is of type
  `(1, ℤ/ℓℤ)^±` (IUT I, Definition 3.1(f); *Étale Theta*, Definition 2.5). -/
  bad_type : ∀ v (hv : v ∈ VBad),
    AG.IsTypeOneZModPM P.ℓ (localize (sect.sectFin v) O.XKu) (tateX v hv)
  /-- At places over `V_mod^bad`, the local model is a natural model obtained by
  extracting an `ℓ`-th root of the theta function (*Étale Theta*, Definition 2.5,
  through the interface predicate of `TemperedGeometry`). -/
  bad_theta_model : ∀ v (hv : v ∈ VBad),
    TG.IsThetaRootModel P.ℓ (localize (sect.sectFin v) O.XKu) (tateX v hv)
  /-- At places over `V_mod^bad`, the base change `ε_v` of the distinguished cusp `ε`
  is the cusp associated to the canonical generator `±1` of the graph quotient
  (IUT I, Definition 3.1(f); *Étale Theta*, Definition 2.5). -/
  epsilon_graph : ∀ v (hv : v ∈ VBad),
    AG.cuspBaseChange (FinitePlace.embedding (sect.sectFin v).maximalIdeal) O.epsilon =
      TG.canonicalGraphCusp (localize (sect.sectFin v) O.CKu) (tateC v hv)

namespace LocalThetaData

variable {AG TG F E Fbar VBad P} {O : OrbicurveData AG F E Fbar VBad P}

variable (L : LocalThetaData AG TG F E Fbar VBad P O)

end LocalThetaData

end LocalData

end Iut

end AbcAdaptation.Reference
