import ArithmeticTeichmullerSpaces.Act1Scene1.PoleDivisionPointInertia
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaInfinityValuation
import ArithmeticTeichmullerSpaces.Act1Scene1.IutWeierstrassLocalization

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(b),(d),(f); Joshi III `ss:theta-data-fixing2`;
the same seed's rational six-torsion and actual inverse-chart ambient valuation.
fidelity: derives a nonzero rational two-torsion point from the seed's actual
six-torsion source, maps it to the same torsion field, and uses it to prove
that valuation inertia fixing the generic base fixes the actual ell-division
point at every already constructed infinity boundary valuation.
boundary: the inertia hypothesis here is the defining pointwise valuation
inertia condition. Its comparison with actual normalization-prime inertia
and triviality of the translation quotient inertia remain separate proofs.
No two-torsion point or geometry law is supplied by the caller.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve NumberField
open JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

private theorem exists_source_twoTorsion :
    ∃ R : S.E.toAffine.Point, R ≠ 0 ∧ 2 • R = 0 := by
  letI : IsAlgClosed S.Fbar := S.isAlgClosure.isAlgClosed
  have hsix : IutSixTorsionRational (F := S.F) (Fbar := S.Fbar) (E := S.E) := by
    have hcurve : Affine.baseChange S.E S.Fbar =
        (S.E.map (algebraMap S.F S.Fbar)).toAffine := rfl
    cases hcurve
    exact S.global.six_torsion_rational
  obtain ⟨e⟩ := iutWeierstrass_four_global_two_torsion_points_of_six_torsion_rational hsix
  by_cases hzero : (e (0 : Fin 4)).val = 0
  · refine ⟨(e (1 : Fin 4)).val, ?_, (AddSubgroup.torsionBy.nsmul_iff).mp (e 1).property⟩
    intro hOne
    have heq : (1 : Fin 4) = 0 := e.injective (Subtype.ext (hOne.trans hzero.symm))
    norm_num at heq
  · exact ⟨(e (0 : Fin 4)).val, hzero, (AddSubgroup.torsionBy.nsmul_iff).mp (e 0).property⟩

/-- The two-torsion shift is produced from this seed, not a free local point. -/
def infinityTwoTorsionShift : S.prime.EK.toAffine.Point :=
  pointMap S.E (algebraMap S.F ↥S.prime.torsionField) S.exists_source_twoTorsion.choose

theorem infinityTwoTorsionShift_ne_zero : S.infinityTwoTorsionShift ≠ 0 := by
  intro h
  apply S.exists_source_twoTorsion.choose_spec.1
  apply pointMap_injective S.E (algebraMap S.F ↥S.prime.torsionField)
  exact h.trans (map_zero _).symm

theorem infinityTwoTorsionShift_two_nsmul : 2 • S.infinityTwoTorsionShift = 0 := by
  rw [infinityTwoTorsionShift, ← map_nsmul, S.exists_source_twoTorsion.choose_spec.2, map_zero]

/-- At the actual infinity valuation, base-fixing valuation inertia fixes the actual division point. -/
theorem infinityAmbientValuation_inertia_fixes_divSys
    (pm : Bool) (q : S.infinityFiber pm) (σ : Genuine.Gal S.prime.EK)
    (hσ : ∀ a ∈ S.infinityAmbientValuation pm q,
      (S.infinityAmbientValuation pm q).valuation (σ a - a) < 1)
    (hG : Genuine.act S.prime.EK σ (Genuine.genericPoint S.prime.EK) =
      Genuine.genericPoint S.prime.EK) :
    Genuine.act S.prime.EK σ (Genuine.divSys S.prime.EK S.prime.ℓ) =
      Genuine.divSys S.prime.EK S.prime.ℓ :=
  PoleDivisionPointInertia.inertia_fixes_of_nsmul_pole S.prime.EK
    (S.infinityAmbientValuation pm q) (S.infinityAmbientValuation_constant_mem pm q)
    (Genuine.σk S.prime.EK σ) hσ S.prime.ℓ S.prime.ℓ_prime.pos
    (S.prime.ℓ_prime.odd_of_ne_two (by have h := S.prime.five_le; omega))
    S.infinityTwoTorsionShift S.infinityTwoTorsionShift_ne_zero S.infinityTwoTorsionShift_two_nsmul
    (Genuine.nonsingular_generic S.prime.EK)
    (S.infinityAmbientValuation_xG_not_mem pm q) hG
    (Genuine.divSys S.prime.EK S.prime.ℓ)
    (Genuine.nsmul_divSys S.prime.EK S.prime.ℓ S.prime.ℓ_prime.pos)

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
