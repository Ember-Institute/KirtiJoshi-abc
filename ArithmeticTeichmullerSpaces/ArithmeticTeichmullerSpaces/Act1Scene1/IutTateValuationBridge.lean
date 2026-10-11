/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/SL2Image.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `a2c25b2edbf5a9cbc30588b466a738b49547b443`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: ports the generic valued-field Tate-parameter lemmas used by
the mod-`ell` image argument to the local Scene1 namespace.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutTateParameterCompletion

/-!
source-id: IUT-COR312-TATE-VALUATION-BRIDGE
source: the `Valued` section of `refer/iut/Iut/Concrete/SL2Image.lean`.
fidelity: transfers equality of completion norms to equality of valuations,
identifies a norm-uniformizer valuation, computes the valuation of a Tate
parameter from its ordered exponent, and proves `v(q) = v(j)⁻¹`.
These are local valuation facts; they do not prove a Tate structure exists at
any particular place or imply an `SL₂` image condition.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField TateCurvesTheta WeierstrassCurve
open WithZero
open JoshiTeich.ReferenceIut
open scoped WithZero Valued MatrixGroups Classical NumberField

universe u

noncomputable section

variable {k : Type u} [Field k] [NumberField k]
variable {w : NumberField.FinitePlace k}

lemma iutValued_eq_of_norm_eq {x y : localCompletion w} (h : ‖x‖ = ‖y‖) :
    Valued.v x = Valued.v y :=
  le_antisymm (Valued.toNormedField.norm_le_iff.mp h.le)
    (Valued.toNormedField.norm_le_iff.mp h.ge)

lemma iutValued_embedding (x : k) :
    Valued.v (NumberField.FinitePlace.embedding w.maximalIdeal x : localCompletion w) =
      w.maximalIdeal.valuation k x := by
  rw [NumberField.FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']

lemma iutValued_of_isUniformizer {π : localCompletion w} (hπ : IsUniformizer π) :
    Valued.v π = exp (-1 : ℤ) := by
  obtain ⟨π₀, hπ₀⟩ := w.maximalIdeal.valuation_exists_uniformizer k
  have h0 : Valued.v (NumberField.FinitePlace.embedding w.maximalIdeal π₀ : localCompletion w) =
      exp (-1 : ℤ) := by
    rw [iutValued_embedding, hπ₀]
  have hne : (NumberField.FinitePlace.embedding w.maximalIdeal π₀ : localCompletion w) ≠ 0 := by
    intro h
    rw [h, map_zero] at h0
    exact exp_ne_zero h0.symm
  obtain ⟨m, hm⟩ := hπ.generates (Units.mk0 _ hne)
  have hπ0 : Valued.v π ≠ 0 := (Valuation.ne_zero_iff _).mpr hπ.ne_zero
  have hexp : Valued.v π = exp (log (Valued.v π)) := (exp_log hπ0).symm
  have h1 : Valued.v (NumberField.FinitePlace.embedding w.maximalIdeal π₀ : localCompletion w) =
      Valued.v (π ^ m) := iutValued_eq_of_norm_eq (by rw [norm_zpow]; exact hm)
  rw [h0, map_zpow₀, hexp, ← exp_zsmul, exp_inj, smul_eq_mul] at h1
  have hlt : Valued.v π < 1 := (norm_lt_one_iff_valued w π).mp hπ.norm_lt_one
  rw [hexp, ← exp_zero, exp_lt_exp] at hlt
  have hmul : (-log (Valued.v π)) * m = 1 := by linear_combination h1
  have hone := Int.eq_one_of_mul_eq_one_right (by omega) hmul
  rw [hexp]
  congr 1
  omega

lemma iutValued_q_toOrdered
    {E : WeierstrassCurve (localCompletion w)}
    (t : TateParameter (localCompletion w)) {π : localCompletion w}
    (hπ : IsUniformizer π) :
    Valued.v (t.q : localCompletion w) =
      exp (-((t.toOrdered hπ).orderNat : ℤ)) := by
  have h := iutValued_eq_of_norm_eq (x := (t.q : localCompletion w))
    (y := π ^ (t.toOrdered hπ).orderNat)
    (by rw [norm_pow]; exact t.norm_q_eq_pow_orderNat hπ)
  rw [h, map_pow, iutValued_of_isUniformizer hπ, ← exp_nsmul]
  congr 1
  simp

lemma iutValued_q_eq_inv_tateJ
    {E : WeierstrassCurve (localCompletion w)}
    (t : TateParameter (localCompletion w)) :
    Valued.v (t.q : localCompletion w) = (Valued.v t.tateJ)⁻¹ := by
  have h := iutValued_eq_of_norm_eq (x := t.tateJ)
    (y := (t.q : localCompletion w)⁻¹)
    (by rw [norm_inv]; exact t.norm_tateJ (twelve_ne_zero w))
  rw [h, map_inv₀, inv_inv]

end

end JoshiTeich.Act1Scene1
