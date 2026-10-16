import ArithmeticTeichmullerSpaces.Act1Scene1.IutGeometricTorsionBasis
import ArithmeticTeichmullerSpaces.Act1Scene1.IutWeierstrassLocalization

/-!
source-id: JT-SCENE1-SIX-TORSION-TATE-ROOT
source: initial theta data's rational six-torsion, geometric torsion count
and the existing Tate residue homomorphism.
fidelity: all 36 geometric six-torsion points descend to the base field.
An injective localization into an actual Tate uniformization therefore
forces a sixth root of that uniformization's Tate parameter.
boundary: Scene1/Derived; no q-order size or BK/volume conclusion assumed.
-/

namespace JoshiTeich.Act1Scene1
open WeierstrassCurve
open scoped Classical
universe u v w
noncomputable section
variable {F : Type u} [Field F] [NumberField F]
variable {Fbar : Type v} [Field Fbar] [Algebra F Fbar] [IsAlgClosed Fbar]
variable {E : WeierstrassCurve F} [E.IsElliptic]

theorem sixTorsion_card_of_rational
    (hsix : IutSixTorsionRational (F := F) (Fbar := Fbar) (E := E)) :
    Nat.card (iutTorsion E.toAffine.Point 6) = 36 := by
  letI : CharZero Fbar := charZero_of_injective_ringHom (algebraMap F Fbar).injective
  let f := iutWeierstrassPointMap (E := E) (algebraMap F Fbar)
  let g : iutTorsion E.toAffine.Point 6 → iutTorsion (E.map (algebraMap F Fbar)).toAffine.Point 6 :=
    fun P => ⟨f P.1, AddSubgroup.torsionBy.nsmul_iff.mpr (by
      rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp P.2, map_zero])⟩
  have hi : Function.Injective g := by
    intro P Q h
    exact Subtype.ext (iutWeierstrassPointMap_injective (E := E) (algebraMap F Fbar)
      (congrArg Subtype.val h))
  have hs : Function.Surjective g := by
    intro Q
    obtain ⟨P, hP⟩ := hsix Q.1 Q.2
    have hp : P ∈ iutTorsion E.toAffine.Point 6 := by
      rw [AddSubgroup.torsionBy.nsmul_iff]
      apply iutWeierstrassPointMap_injective (E := E) (algebraMap F Fbar)
      change f (6 • P) = f 0
      rw [map_nsmul, hP, AddSubgroup.torsionBy.nsmul_iff.mp Q.2, map_zero]
    exact ⟨⟨P, hp⟩, Subtype.ext hP⟩
  rw [Nat.card_congr (Equiv.ofBijective g ⟨hi, hs⟩)]
  exact (iutGeometricTorsion_card (E.map (algebraMap F Fbar)) 6 (by decide)).trans (by norm_num)

theorem exists_sixth_root_of_rational_six_torsion
    {K : Type w} [NormedField K] {A : Type*} [AddCommGroup A]
    (S : IutTateQuotientUniformization K A)
    (f : E.toAffine.Point →+ A) (hf : Function.Injective f)
    (hsix : IutSixTorsionRational (F := F) (Fbar := Fbar) (E := E)) :
    ∃ r : K, r ^ 6 = (S.q : K) := by
  haveI : NeZero (6 : ℕ) := ⟨by decide⟩
  haveI : Finite (iutTorsion A 6) := S.finite_torsion
  let g : iutTorsion E.toAffine.Point 6 → iutTorsion A 6 :=
    fun P => ⟨f P.1, AddSubgroup.torsionBy.nsmul_iff.mpr (by
      rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp P.2, map_zero])⟩
  have hi : Function.Injective g := by
    intro P Q h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  have hc : 6 * 6 ≤ Nat.card (iutTorsion A 6) := by
    have h := Nat.card_le_card_of_injective g hi
    rw [sixTorsion_card_of_rational hsix] at h
    exact h
  obtain ⟨r, m, hr⟩ := S.exists_root_class_values_of_torsion_card (by decide : 0 < 6) hc
  exact IutQRootExistence.exists_pow_eq_of_root_class_of_nonzero (by decide : 0 < 6) S.q.ne_zero hr

end
end JoshiTeich.Act1Scene1
