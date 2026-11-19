/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/ThetaLocalConstruct/Data.lean
-/
import Solutions.Source_ReferenceIutConcreteThetaRegion
import Solutions.Source_ReferenceIutTateCompat
import Solutions.Source_ReferenceIutTateRoots
import Solutions.Source_SL2ImageLocalTorsion
import Solutions.Source_TripodPlaceUnder

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField WeierstrassCurve Anabelian
open scoped Classical

universe u

noncomputable section

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (D : InitialThetaData AG TG)

/-- The places of the torsion field above the selected bad places of the moduli field. -/
abbrev IsBadK (v : FinitePlace D.Kt) : Prop :=
  IsBadPlace D.E D.prime.torsionField D.VBad v

/-- The base curve has four rational points killed by multiplication by `2`. -/
abbrev TwoTorsionRational : Prop :=
  2 * 2 ≤ Nat.card ↥(AddSubgroup.torsionBy D.E.toAffine.Point ((2 : ℕ) : ℤ))

private theorem isBadPlace_iff_exists_liesOver {F Fbar : Type u} [Field F] [NumberField F]
    [Field Fbar] [Algebra F Fbar] (E : WeierstrassCurve F) [E.IsElliptic]
    (K : IntermediateField F Fbar) [NumberField ↥K]
    (VBad : Set (FinitePlace ↥(fieldOfModuli F E))) (v : FinitePlace ↥K) :
    IsBadPlace E K VBad v ↔
      ∃ w ∈ badPlacesOver F E VBad, FinitePlace.LiesOver v w := by
  letI : Algebra ↥(fieldOfModuli F E) ↥K := (fieldOfModuli F E).instAlgebraSubtypeMem
  have hmap : algebraMap ↥(fieldOfModuli F E) ↥K =
      (algebraMap F ↥K).comp (algebraMap ↥(fieldOfModuli F E) F) :=
    RingHom.ext fun _ => rfl
  haveI : IsScalarTower (𝓞 ↥(fieldOfModuli F E)) (𝓞 F) (𝓞 ↥K) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      apply RingOfIntegers.coe_injective
      exact RingHom.congr_fun hmap x)
  constructor
  · rintro ⟨w₀, hw₀, hvw₀⟩
    refine ⟨Tripod.placeUnder v, ⟨w₀, hw₀, ⟨?_⟩⟩, Tripod.liesOver_placeUnder v⟩
    rw [hvw₀.over, Tripod.placeUnder_maximalIdeal, Ideal.under_def, Ideal.under_def,
      Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  · rintro ⟨w, ⟨w₀, hw₀, hww₀⟩, hvw⟩
    haveI : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hvw
    haveI : w.maximalIdeal.asIdeal.LiesOver w₀.maximalIdeal.asIdeal := hww₀
    exact ⟨w₀, hw₀, ⟨(Ideal.LiesOver.trans
      v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal w₀.maximalIdeal.asIdeal).over⟩⟩

lemma isBadK_of_liesOver {v : FinitePlace D.Kt} {w : FinitePlace D.F}
    (hvw : FinitePlace.LiesOver v w) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    IsBadK D v :=
  (isBadPlace_iff_exists_liesOver D.E D.prime.torsionField D.VBad v).mpr ⟨w, hw, hvw⟩

lemma exists_liesOver_of_isBadK {v : FinitePlace D.Kt} (hv : IsBadK D v) :
    ∃ w ∈ badPlacesOver D.F D.E D.VBad, FinitePlace.LiesOver v w :=
  (isBadPlace_iff_exists_liesOver D.E D.prime.torsionField D.VBad v).mp hv

private theorem card_torsionBy_le_of_injective {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (hf : Function.Injective f) (n : ℕ)
    [Finite ↥(AddSubgroup.torsionBy B (n : ℤ))] :
    Nat.card ↥(AddSubgroup.torsionBy A (n : ℤ)) ≤
      Nat.card ↥(AddSubgroup.torsionBy B (n : ℤ)) := by
  let onTorsion (P : AddSubgroup.torsionBy A (n : ℤ)) : AddSubgroup.torsionBy B (n : ℤ) :=
    ⟨f P.1, by rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul,
      AddSubgroup.torsionBy.nsmul_iff.mp P.2, map_zero]⟩
  exact Nat.card_le_card_of_injective onTorsion
    (fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h)))

private theorem pointMap_injective {k K : Type*} [Field k] [Field K]
    (E : WeierstrassCurve k) (f : k →+* K) : Function.Injective (pointMap E f) := by
  letI := f.toAlgebra
  exact Affine.Point.map_injective (W' := E) (S := k) (F := k) (K := K) (Algebra.ofId k K)

private def curveOfThetaData : EllipticCurveData.{u} where
  F := D.F
  Fbar := D.Fbar
  E := D.E

private def representationOfThetaData : (curveOfThetaData D).ModEllRepData D.ℓ where
  torsionBasis := D.prime.torsionBasis
  rep := D.prime.rep
  rep_spec := D.prime.rep_spec
  ker_isOpen := D.prime.ker_isOpen

/-- The chosen local Tate curve has a `2ℓ`-th root of its parameter. -/
theorem exists_qroot (htwo : TwoTorsionRational D)
    {v : FinitePlace D.Kt} (hv : IsBadK D v) :
    ∃ x : localCompletion v, x ^ (2 * D.ℓ) = ((D.tate.S v hv).t.q : localCompletion v) := by
  haveI : NeZero D.ℓ := ⟨D.prime.ℓ_prime.ne_zero⟩
  let S := D.tate.S v hv
  have hℓ2 : D.ℓ ≠ 2 := by
    have h5 : 5 ≤ D.ℓ := D.prime.five_le
    exact ne_of_gt ((by decide : 2 < 5).trans_le h5)
  have hℓ : D.ℓ * D.ℓ ≤
      Nat.card ↥(TateStructure.torsion D.ℓ (curveKw D.E D.prime.torsionField v)) :=
    @EllipticCurveData.card_torsion_curveKw_ge (curveOfThetaData D) D.ℓ
      (representationOfThetaData D) v (S.finite_torsion D.ℓ)
  have h2 : 2 * 2 ≤ Nat.card ↥(TateStructure.torsion 2 (curveKw D.E D.prime.torsionField v)) := by
    let toCompletion := (emb D.prime.torsionField v).comp (algebraMap D.F D.Kt)
    haveI : Finite ↥(TateStructure.torsion 2 (D.E.map toCompletion)) := S.finite_torsion 2
    exact htwo.trans (card_torsionBy_le_of_injective (pointMap D.E toCompletion)
      (pointMap_injective D.E toCompletion) 2)
  exact S.exists_pow_eq_q D.ℓ (D.prime.ℓ_prime.odd_of_ne_two hℓ2) hℓ h2

variable (htwo : TwoTorsionRational D)

/-- A `2ℓ`-th root at each bad place, with value `1` at all other places. -/
def qrootOf (v : FinitePlace D.Kt) : localCompletion v :=
  if hv : IsBadK D v then Classical.choose (exists_qroot D htwo hv) else 1

lemma qrootOf_spec {v : FinitePlace D.Kt} (hv : IsBadK D v) :
    qrootOf D htwo v ^ (2 * D.ℓ) = ((D.tate.S v hv).t.q : localCompletion v) := by
  unfold qrootOf
  rw [dif_pos hv]
  exact Classical.choose_spec (exists_qroot D htwo hv)

lemma qrootOf_of_not {v : FinitePlace D.Kt} (hv : ¬ IsBadK D v) : qrootOf D htwo v = 1 := by
  unfold qrootOf
  rw [dif_neg hv]

/-- The comparison map used for the local data of the fixed initial datum. -/
abbrev embedFOf (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (h : FinitePlace.LiesOver v w) : localCompletion w →+* localCompletion v :=
  embedCompletion h

/-- The chosen root powers to the image of the Tate parameter on the base completion. -/
lemma qrootOf_pow (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (h : FinitePlace.LiesOver v w) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    qrootOf D htwo v ^ (2 * D.ℓ) =
      embedFOf D v w h ((D.prime.tate w hw).q : localCompletion w) := by
  have hv := isBadK_of_liesOver D h hw
  rw [qrootOf_spec D htwo hv]
  exact TateStructure.t_q_eq_embedCompletion h (D.tate.S v hv) (D.prime.tate w hw)
    (D.prime.tateJ_eq w hw)

lemma qrootOf_ne_zero (v : FinitePlace D.Kt) : qrootOf D htwo v ≠ 0 := by
  by_cases hv : IsBadK D v
  · intro h0
    have hpow := qrootOf_spec D htwo hv
    have hℓ : D.ℓ ≠ 0 := D.prime.ℓ_prime.ne_zero
    rw [h0, zero_pow (Nat.mul_ne_zero (by decide) hℓ)] at hpow
    exact Units.ne_zero _ hpow.symm
  · rw [qrootOf_of_not D htwo hv]
    exact one_ne_zero

end

end AbcAdaptation.Reference.Iut
