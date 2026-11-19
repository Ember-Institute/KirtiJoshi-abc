namespace AbcAdaptation.Tripod
open WeierstrassCurve NumberField
open scoped IntermediateField

open AbcAdaptation.Reference.Iut

noncomputable def curveOf (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) :
    EllipticCurveData :=
  letI := finiteDimensional_fieldOfExtended h3 h5
  { F := fieldOf' x.1
    Fbar := Qbar
    E := legendre (gen' x.1)
    isElliptic := legendre_gen'_isElliptic x }

end AbcAdaptation.Tripod
