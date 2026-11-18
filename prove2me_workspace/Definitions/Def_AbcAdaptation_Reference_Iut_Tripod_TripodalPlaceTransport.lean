/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository: https://github.com/lana-agents/iut
Original revision recorded by current adaptation: 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Source declarations selected from the original proof; imports and namespaces adapted.
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FieldTransport
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_FinitePlaceResidueTransport

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real Classical

variable (P : CurveProviders) (x : Pt)

theorem genT_ne_zero : genT P x ≠ 0 := fun h => gen'_ne_zero x.2.1 (congrArg Subtype.val h)

theorem genT_sub_one_ne_zero : genT P x - 1 ≠ 0 := by
  intro h
  exact gen'_ne_one x.2.2 (congrArg Subtype.val (sub_eq_zero.mp h))

theorem tpdEquiv_symm_gen : (tpdEquiv P x).symm (gen x.1) = genT P x := by
  rw [← tpdEquiv_genT, AlgEquiv.symm_apply_apply]

noncomputable abbrev tpdPlace (𝔭 : FinitePlace (tpd P x)) : FinitePlace (fieldOf x.1) :=
  FinitePlace.mapEquiv (tpdEquiv P x : tpd P x ≃+* fieldOf x.1) 𝔭

theorem tpdPlace_gen (𝔭 : FinitePlace (tpd P x)) : tpdPlace P x 𝔭 (gen x.1) = 𝔭 (genT P x) := by
  rw [tpdPlace, FinitePlace.mapEquiv_apply]
  congr 1
  exact tpdEquiv_symm_gen P x

theorem tpdPlace_gen_sub_one (𝔭 : FinitePlace (tpd P x)) :
    tpdPlace P x 𝔭 (gen x.1 - 1) = 𝔭 (genT P x - 1) := by
  rw [tpdPlace, FinitePlace.mapEquiv_apply, map_sub, map_one]
  congr 2
  exact tpdEquiv_symm_gen P x

theorem residueChar_tpdPlace (𝔭 : FinitePlace (tpd P x)) :
    residueChar (tpdPlace P x 𝔭) = residueChar 𝔭 :=
  FinitePlace.mapEquiv_residueChar _ _

end AbcAdaptation.Tripod
