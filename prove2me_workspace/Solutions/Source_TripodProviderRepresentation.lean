/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 10e40d2e52a8e7220c2a90ff1595f5b385f987ef
Original paths Iut/Tripod/Providers.lean and Iut/Concrete/ModEllRepConstruct.lean
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaModEllRepConstruct
import Solutions.Source_TripodTorsionBasis
import Solutions.Source_TripodUnramifiedBase

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference.Iut WeierstrassCurve
open scoped Classical

private theorem curveOf_baseChange (x : Pt) (h3 : TorsionFinite x.1 3)
    (h5 : TorsionFinite x.1 5) :
    Affine.baseChange (curveOf x h3 h5).E (curveOf x h3 h5).Fbar = legendre x.1 := by
  change Affine.baseChange (legendre (gen' x.1)) Qbar = legendre x.1
  exact legendre_baseChange (L := Qbar) (gen' x.1)

/-- The mod-`ℓ` representation on the geometric torsion of the Legendre curve over `F_λ`. -/
noncomputable def modRep_curveOf (x : Pt) (h3 : TorsionFinite x.1 3)
    (h5 : TorsionFinite x.1 5) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    (curveOf x h3 h5).ModEllRepData ℓ := by
  let C := curveOf x h3 h5
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  letI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hbase : Affine.baseChange C.E C.Fbar = legendre x.1 := curveOf_baseChange x h3 h5
  have hbasis : Nonempty (AddSubgroup.torsionBy (Affine.baseChange C.E C.Fbar).Point ℓ ≃+
      (Fin 2 → ZMod ℓ)) := by
    rw [hbase]
    exact legendre_torsionBasis x ℓ
  let R := JoshiTeich.Act1Scene1.IutCurveModEllRepData.ofBasis C.E C.Fbar ℓ hbasis
  exact
    { torsionBasis := R.torsionBasis
      rep := R.rep
      rep_spec := R.rep_spec
      ker_isOpen := R.ker_isOpen }

/-- Supply the Legendre curve data from the arithmetic of the curves over `F_λ`. -/
noncomputable def CurveProviders.ofArithmetic
    (arith : ∀ x : Pt, (curveOf x (legendre_torsionFinite x.1 3 (by decide))
      (legendre_torsionFinite x.1 5 (by decide))).CurveArithmetic) : CurveProviders where
  torsionFinite3 l := legendre_torsionFinite l 3 (by decide)
  torsionFinite5 l := legendre_torsionFinite l 5 (by decide)
  arith := arith
  modRep x ℓ hℓ := modRep_curveOf x _ _ ℓ hℓ

end AbcAdaptation.Tripod
