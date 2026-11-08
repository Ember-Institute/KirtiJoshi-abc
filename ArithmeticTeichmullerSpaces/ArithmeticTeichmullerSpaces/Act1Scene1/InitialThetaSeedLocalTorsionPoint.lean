import ArithmeticTeichmullerSpaces.Act1Scene1.TateQRootExactOrder
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSeedQRootValuation

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut
open NumberField WeierstrassCurve
open scoped Classical

universe u

noncomputable section

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-!
source-id: IUT-COR312-TATE-TORSION-RESIDUE
source: Joshi III `ss:theta-data-fixing2`, the paragraph "Existence of
local torsion points of order 2 ell" (TeX lines 1062--1064); the proved
seed q-root source and the actual derived Tate quotient uniformization.
fidelity: maps the seed's same completion-valued 2 ell-th root of the Tate
parameter to a point of its actual local elliptic curve, proves exact
additive order 2 ell and nonvanishing, and specializes to the seed's
valuation section. No additional root, point, or geometry law is supplied.
boundary: Scene1/Derived; restricted to the supplied VBad and the same seed.
This does not identify paper representative carriers, construct an orbicurve
or theta-root model, or close the InitialThetaGeometryProducer obligation.
-/

/-- The unit power equation for the root of the seed's derived Tate parameter. -/
private theorem localTorsionPoint_rootUnit_pow
    (S : InitialThetaGeometrySeed AG TG)
    (w : S.torsionQRootSource.badFinset) :
    (Units.mk0 (S.torsionQRootSource.qroot w)
      (S.torsionQRootSource.qroot_ne_zero w)) ^ (2 * S.prime.ℓ) =
      (S.tate.S w.1 (S.torsionQRootSource_badPlace w)).t.q := by
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using
    S.torsionQRootSource_qroot_pow_eq_tate w

/-- The root gives a point on the actual local elliptic curve in the derived family. -/
def localTorsionPoint
    (S : InitialThetaGeometrySeed AG TG)
    (w : S.torsionQRootSource.badFinset) :
    (curveKw S.E S.prime.torsionField w.1).toAffine.Point :=
  (IutTateQuotientUniformization.ofTateStructure
    (S.tate.S w.1 (S.torsionQRootSource_badPlace w))).ofUnit
      (Units.mk0 (S.torsionQRootSource.qroot w)
        (S.torsionQRootSource.qroot_ne_zero w))

/-- The local point has exact order 2 ell, not merely order dividing 2 ell. -/
theorem localTorsionPoint_addOrderOf
    (S : InitialThetaGeometrySeed AG TG)
    (w : S.torsionQRootSource.badFinset) :
    addOrderOf (S.localTorsionPoint w) = 2 * S.prime.ℓ := by
  exact (IutTateQuotientUniformization.ofTateStructure
    (S.tate.S w.1 (S.torsionQRootSource_badPlace w))).addOrderOf_ofUnit_eq_of_pow_eq_q
      (S.localTorsionPoint_rootUnit_pow w)

theorem localTorsionPoint_ne_zero
    (S : InitialThetaGeometrySeed AG TG)
    (w : S.torsionQRootSource.badFinset) :
    S.localTorsionPoint w ≠ 0 := by
  intro hZero
  have hOrder := S.localTorsionPoint_addOrderOf w
  rw [hZero, addOrderOf_zero] at hOrder
  have hFive := S.prime.five_le
  omega

/-- The seed's selected representative consumes the same local point construction. -/
def selectedLocalTorsionPoint
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    (curveKw S.E S.prime.torsionField (S.valuationSection.sectFin v)).toAffine.Point :=
  S.localTorsionPoint (S.selectedQRootPlace v hv)

theorem selectedLocalTorsionPoint_addOrderOf
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    addOrderOf (S.selectedLocalTorsionPoint v hv) = 2 * S.prime.ℓ :=
  S.localTorsionPoint_addOrderOf (S.selectedQRootPlace v hv)

theorem selectedLocalTorsionPoint_ne_zero
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    S.selectedLocalTorsionPoint v hv ≠ 0 :=
  S.localTorsionPoint_ne_zero (S.selectedQRootPlace v hv)

end

end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
