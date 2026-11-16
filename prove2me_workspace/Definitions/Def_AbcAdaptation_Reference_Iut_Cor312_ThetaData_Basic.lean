/-
Adaptation provenance: this block was inserted by the adaptation; it is not an original source notice.
Original source path: Iut/Cor312/ThetaData/Basic.lean
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
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_AdmissiblePrime
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_LocalConditions
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Orbicurve
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateFamily

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

namespace AbcAdaptation.Reference

/-!
# Initial Θ-data (taxis #38; IUT I, Definition 3.1)

The assembled notion of **initial Θ-data**: the tuple

`(F̄/F, X_F, ℓ, C̲_K, V, V_mod^bad, ε)`

of IUT I, Definition 3.1(a)–(f), packaged from the child modules:

* global field and elliptic curve, Definition 3.1(a)–(b): taxis #39
  (`Iut.IsInitialThetaGlobalData`);
* admissible prime and `ℓ`-torsion field, Definition 3.1(b)–(c): taxis #40
  (`Iut.AdmissiblePrimeData`);
* orbicurves, `K`-core, and distinguished cusp, Definition 3.1(d)/(f): taxis #41
  (`Iut.OrbicurveData`);
* valuation section and local conditions, Definition 3.1(e)–(f): taxis #42
  (`Iut.LocalThetaData`, containing `V` as `Iut.ValuationSection`).

## Chosen data vs derived objects

The **chosen data** are exactly the fields of this structure and of its child
structures: `F`, `F̄`, `E_F` (giving `X_F = E_F ∖ {0}` through the anabelian
interface), `V_mod^bad`, `ℓ` with the basis/representation of the `ℓ`-torsion, `C̲_K`
with `X̲_K` and the element of `Q` giving `ε`, the valuation section `V`, and the local
choices (decomposition groups). The **derived objects** are `def`s, never fields:
`F_mod = ℚ(j(E))` (`Iut.fieldOfModuli`), `F_sol` (`Iut.solvableClosure`), `K`
(`AdmissiblePrimeData.torsionField`, the fixed field of the kernel of the mod-`ℓ`
representation), the good/bad place sets (`Iut.badPlacesOver`, `Iut.goodModPlaces`,
`ValuationSection.Vbad`, …), the localizations (`Iut.localize`, `Iut.localCompletion`),
the associated covers' fundamental-group maps (`AnabelianGeometry.pi1Cover`), and the
`Π_v` conventions (`LocalThetaData.PivBad`/`PivGood`).

Existence of initial Θ-data is **not** asserted anywhere (statement project;
taxis #38). No hypothesis beyond Definition 3.1 is imposed; in particular, following
IUT I, Remark 3.1.5, `K/F_mod` is not required to be Galois.

The `NumberField` structure on `K` and the `F_mod`-algebra structure on `K` (with its
scalar-tower compatibility, which pins it uniquely) are carried as instance fields;
the former is provable from the openness of the kernel
(`AdmissiblePrimeData.numberField_torsionField`), and being propositional classes,
carrying them is proof-irrelevant.
-/

namespace Iut

universe u

open NumberField WeierstrassCurve OrbicurveDataSection

/-- **Initial Θ-data** (IUT I, Definition 3.1; taxis #38): the packaged tuple
`(F̄/F, X_F, ℓ, C̲_K, V, V_mod^bad, ε)` relative to an anabelian interface `AG` and
tempered interface `TG`. See the module docstring for the chosen-data/derived-object
inventory and the honesty boundary. -/
structure InitialThetaData (AG : AnabelianGeometry.{u}) (TG : TemperedGeometry AG) :
    Type (u + 1) where
  /-- The number field `F` (IUT I, Definition 3.1(a)). -/
  F : Type u
  /-- `F` is a field. -/
  [fieldF : Field F]
  /-- `F` is a number field. -/
  [numberFieldF : NumberField F]
  /-- The chosen algebraic closure `F̄` of `F` (IUT I, Definition 3.1(a)). -/
  Fbar : Type u
  /-- `F̄` is a field. -/
  [fieldFbar : Field Fbar]
  /-- `F̄` is an `F`-algebra. -/
  [algebraFbar : Algebra F Fbar]
  /-- `F̄` is an algebraic closure of `F`. -/
  [isAlgClosure : IsAlgClosure F Fbar]
  /-- The elliptic curve `E_F/F`, giving the once-punctured curve
  `X_F = E_F ∖ {0}` (IUT I, Definition 3.1(a)). -/
  E : WeierstrassCurve F
  /-- `E_F` is an elliptic curve. -/
  [isElliptic : E.IsElliptic]
  /-- The chosen nonempty set `V_mod^bad` of nonarchimedean places of `F_mod`
  (IUT I, Definition 3.1(b)). -/
  VBad : Set (FinitePlace ↥(fieldOfModuli F E))
  /-- The global conditions of Definition 3.1(a)–(b) (taxis #39). -/
  global : IsInitialThetaGlobalData F E Fbar VBad
  /-- The admissible prime `ℓ` with the mod-`ℓ` representation data and coprimality
  conditions of Definition 3.1(b)–(c) (taxis #40). -/
  prime : AdmissiblePrimeData F E Fbar VBad
  /-- The `NumberField` structure on `K` (provable:
  `AdmissiblePrimeData.numberField_torsionField`; carried for instance availability,
  proof-irrelevant). -/
  [numberFieldK : NumberField ↥prime.torsionField]
  /-- The `F_mod`-algebra structure on `K`. -/
  [algebraModK : Algebra ↥(fieldOfModuli F E) ↥prime.torsionField]
  /-- Compatibility of the `F_mod`-algebra structure with the inclusions
  `F_mod ⊆ F ⊆ K`, pinning it uniquely. -/
  [towerModK : IsScalarTower ↥(fieldOfModuli F E) F ↥prime.torsionField]
  /-- The Tate uniformizations of `E` over the completions of `K` at the places over
  `V_mod^bad`, Galois-equivariant on the ℓ-torsion (Definition 3.1(f) refers to them;
  chosen data pinned by the coordinates of the Tate parametrization, `Iut.TateFamily`). -/
  tate : TateFamily E prime.torsionField prime.ℓ VBad
  /-- The orbicurve data `C̲_K`, `X̲_K`, `ε` of Definition 3.1(d)/(f) (taxis #41). -/
  orb : OrbicurveData AG F E Fbar VBad prime
  /-- The valuation section `V` and local conditions of Definition 3.1(e)–(f)
  (taxis #42). -/
  localData : LocalThetaData AG TG F E Fbar VBad prime orb

namespace InitialThetaData

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

attribute [instance] fieldF numberFieldF fieldFbar algebraFbar isAlgClosure isElliptic
  numberFieldK algebraModK towerModK

variable (D : InitialThetaData AG TG)

/-- The prime `ℓ` of the Θ-data. -/
def ℓ : ℕ := D.prime.ℓ

end InitialThetaData

end Iut

end AbcAdaptation.Reference
