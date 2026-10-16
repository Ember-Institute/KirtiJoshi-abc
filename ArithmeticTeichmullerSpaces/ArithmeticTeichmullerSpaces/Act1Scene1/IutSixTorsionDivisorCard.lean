import ArithmeticTeichmullerSpaces.Act1Scene1.IutSixTorsionTateRoot

/-!
source-id: JT-SCENE1-SIX-TORSION-DIVISOR-CARD
source: original rational six-torsion and geometric torsion count.
fidelity: for every positive divisor n of six, all geometric n-torsion
points descend and the base field has exactly n squared such points.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1
open WeierstrassCurve
open scoped Classical
universe u v
noncomputable section
variable {F : Type u} [Field F] [NumberField F]
variable {Fbar : Type v} [Field Fbar] [Algebra F Fbar] [IsAlgClosed Fbar]
variable {E : WeierstrassCurve F} [E.IsElliptic]

theorem torsion_card_of_rational_six_divisor
    (hsix : IutSixTorsionRational (F := F) (Fbar := Fbar) (E := E))
    (n : ℕ) (hn0 : 0 < n) (hn : n ∣ 6) :
    Nat.card (iutTorsion E.toAffine.Point n) = n ^ 2 := by
  letI : CharZero Fbar := charZero_of_injective_ringHom (algebraMap F Fbar).injective
  let f := iutWeierstrassPointMap (E := E) (algebraMap F Fbar)
  let g : iutTorsion E.toAffine.Point n → iutTorsion (E.map (algebraMap F Fbar)).toAffine.Point n :=
    fun P => ⟨f P.1, AddSubgroup.torsionBy.nsmul_iff.mpr (by
      rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp P.2, map_zero])⟩
  have hi : Function.Injective g := by
    intro P Q h
    exact Subtype.ext (iutWeierstrassPointMap_injective (E := E) (algebraMap F Fbar)
      (congrArg Subtype.val h))
  have hs : Function.Surjective g := by
    intro Q
    obtain ⟨P, hP⟩ := hsix Q.1 (by
      rw [AddSubgroup.torsionBy.nsmul_iff]
      obtain ⟨k, hk⟩ := hn
      rw [hk, mul_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp Q.2, nsmul_zero])
    have hp : P ∈ iutTorsion E.toAffine.Point n := by
      rw [AddSubgroup.torsionBy.nsmul_iff]
      apply iutWeierstrassPointMap_injective (E := E) (algebraMap F Fbar)
      change f (n • P) = f 0
      rw [map_nsmul, hP, AddSubgroup.torsionBy.nsmul_iff.mp Q.2, map_zero]
    exact ⟨⟨P, hp⟩, Subtype.ext hP⟩
  rw [Nat.card_congr (Equiv.ofBijective g ⟨hi, hs⟩)]
  exact (iutGeometricTorsion_card (E.map (algebraMap F Fbar)) n hn0.ne')

end
end JoshiTeich.Act1Scene1
