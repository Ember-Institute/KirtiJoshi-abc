import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSeedLocalTorsionPoint
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaTorsionQuotient

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut
open NumberField WeierstrassCurve
open scoped Classical Valued

universe u

noncomputable section

local instance (priority := 1100)
    {F Fbar : Type u} [Field F] [Field Fbar] [Algebra F Fbar]
    (K : IntermediateField F Fbar) : DecidableEq ↥K :=
  fun a b => Classical.propDecidable (a = b)

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(f); `refer/iut/Iut/Anabelian/LocalInputs.lean`,
`torsion_surj` and `exists_toLocal_eq`; the global/local torsion quotient
comparison in `InitialThetaTorsionQuotient.lean`; Joshi III
`ss:theta-data-fixing2`, the chosen section and the local 2 ell-th root.
fidelity: the double of the same seed's chosen local q-root point is a
canonical ell-torsion point. Its unique global torsion lift has rank-one
class equal to one of the two distinguished classes. The root, section,
Tate family, global torsion group, and quotient all come from the same seed.
boundary: Scene1/Derived; restricted to the supplied VBad, with both signs
retained. No AG.Cusp, orbicurve, theta-root model, or paper-carrier identity
is constructed. Original proofs using the existing local source APIs.
-/

private def selectedRootUnit
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    (localCompletion (S.valuationSection.sectFin v))ˣ :=
  Units.mk0 (S.torsionQRootSource.qroot (S.selectedQRootPlace v hv))
    (S.torsionQRootSource.qroot_ne_zero (S.selectedQRootPlace v hv))

private theorem selectedRootUnit_square_pow
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    (S.selectedRootUnit v hv ^ 2) ^ S.prime.ℓ =
      (S.tate.S (S.valuationSection.sectFin v)
        (S.prime.sectFin_isBad S.tate hv)).t.q := by
  rw [← pow_mul]
  apply Units.ext
  change S.torsionQRootSource.qroot (S.selectedQRootPlace v hv) ^ (2 * S.prime.ℓ) = _
  have h := S.torsionQRootSource_qroot_pow_eq_tate (S.selectedQRootPlace v hv)
  change S.torsionQRootSource.qroot (S.selectedQRootPlace v hv) ^ (2 * S.prime.ℓ) =
    ((S.tate.S (S.valuationSection.sectFin v)
      (S.prime.sectFin_isBad S.tate hv)).t.q :
        localCompletion (S.valuationSection.sectFin v)) at h
  exact h

private theorem localTorsionPoint_eq_ofUnit
    (S : InitialThetaGeometrySeed AG TG)
    (w : S.torsionQRootSource.badFinset)
    (hw : IsBadPlace S.E S.prime.torsionField S.VBad w.1) :
    S.localTorsionPoint w = (S.tate.S w.1 hw).ofUnit
      (Units.mk0 (S.torsionQRootSource.qroot w)
        (S.torsionQRootSource.qroot_ne_zero w)) := by
  have hproof : S.torsionQRootSource_badPlace w = hw := Subsingleton.elim _ _
  have hmap {K : Type u} [Field K]
      [Valued K (WithZero (Multiplicative ℤ))]
      [Valuation.RankOne (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))]
      [CompleteSpace K] {E : WeierstrassCurve K} (T : TateStructure E) (x : Kˣ) :
      (IutTateQuotientUniformization.ofTateStructure T).ofUnit x = T.ofUnit x := rfl
  unfold localTorsionPoint
  rw [hproof]
  exact hmap _ _

private theorem selectedLocalTorsionPoint_two_nsmul_eq_ofUnit
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    2 • S.selectedLocalTorsionPoint v hv =
      (S.tate.S (S.valuationSection.sectFin v)
        (S.prime.sectFin_isBad S.tate hv)).ofUnit
          (S.selectedRootUnit v hv ^ 2) := by
  change 2 • S.localTorsionPoint (S.selectedQRootPlace v hv) = _
  rw [S.localTorsionPoint_eq_ofUnit (S.selectedQRootPlace v hv)
    (S.prime.sectFin_isBad S.tate hv)]
  exact (S.tate.S (S.valuationSection.sectFin v)
    (S.prime.sectFin_isBad S.tate hv)).nsmul_ofUnit 2 (S.selectedRootUnit v hv)

/-- The specific doubled q-root point is canonical for the selected Tate structure. -/
theorem selectedLocalTorsionPoint_two_nsmul_isCanonical
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    (S.tate.S (S.valuationSection.sectFin v)
      (S.prime.sectFin_isBad S.tate hv)).IsCanonical S.prime.ℓ
        (2 • S.selectedLocalTorsionPoint v hv) := by
  rw [S.selectedLocalTorsionPoint_two_nsmul_eq_ofUnit v hv]
  apply (S.tate.S (S.valuationSection.sectFin v)
    (S.prime.sectFin_isBad S.tate hv)).isCanonical_ofUnit S.prime.ℓ (m₁ := 0)
  simpa only [mul_zero, add_zero, zpow_one] using S.selectedRootUnit_square_pow v hv

/-- Package the actual doubled root point in the local ell-torsion subgroup. -/
def doubledLocalTorsionPoint
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    ↥(TateStructure.torsion S.prime.ℓ
      (curveKw S.E S.prime.torsionField (S.valuationSection.sectFin v))) := by
  refine ⟨2 • S.selectedLocalTorsionPoint v hv, ?_⟩
  rw [S.selectedLocalTorsionPoint_two_nsmul_eq_ofUnit v hv]
  apply (S.tate.S (S.valuationSection.sectFin v)
    (S.prime.sectFin_isBad S.tate hv)).ofUnit_mem_torsion S.prime.ℓ (m₁ := 0)
  simpa only [mul_zero, add_zero, zpow_one] using S.selectedRootUnit_square_pow v hv

/-- Lift this particular local point through the existing global/local torsion equivalence. -/
def canonicalGlobalRootPoint
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    ↥S.prime.TK :=
  (S.prime.localTorsionEquiv S.tate (S.prime.sectFin_isBad S.tate hv)).symm
    (S.doubledLocalTorsionPoint v hv)

/-- The global lift localizes to the double of the originally constructed root point. -/
theorem canonicalGlobalRootPoint_toLocal
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    TateFamily.toLocal S.prime (S.valuationSection.sectFin v)
      (S.canonicalGlobalRootPoint v hv : S.prime.EK.toAffine.Point) =
        2 • S.selectedLocalTorsionPoint v hv := by
  have h := (S.prime.localTorsionEquiv S.tate
    (S.prime.sectFin_isBad S.tate hv)).apply_symm_apply
      (S.doubledLocalTorsionPoint v hv)
  exact congrArg Subtype.val h

/-- The lift has the two canonical global classes, with the sign retained. -/
theorem canonicalGlobalRootPoint_rankOneClass
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    S.prime.rankOneClass (S.canonicalGlobalRootPoint v hv) = S.prime.distinguishedClass ∨
      S.prime.rankOneClass (S.canonicalGlobalRootPoint v hv) = -S.prime.distinguishedClass := by
  apply (S.prime.canonical_iff_rankOneClass S.tate hv
    (S.canonicalGlobalRootPoint v hv)).mp
  change (S.tate.S (S.valuationSection.sectFin v)
    (S.prime.sectFin_isBad S.tate hv)).IsCanonical S.prime.ℓ
      (TateFamily.toLocal S.prime (S.valuationSection.sectFin v)
        (S.canonicalGlobalRootPoint v hv : S.prime.EK.toAffine.Point))
  rw [S.canonicalGlobalRootPoint_toLocal v hv]
  exact S.selectedLocalTorsionPoint_two_nsmul_isCanonical v hv

end

end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
