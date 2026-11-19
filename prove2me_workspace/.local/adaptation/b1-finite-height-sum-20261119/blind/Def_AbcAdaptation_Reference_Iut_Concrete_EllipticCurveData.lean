namespace AbcAdaptation.Reference

namespace Iut

universe u v

open NumberField WeierstrassCurve

structure EllipticCurveData : Type (u + 1) where

  F : Type u

  [fieldF : Field F]

  [numberFieldF : NumberField F]

  Fbar : Type u

  [fieldFbar : Field Fbar]

  [algebraFbar : Algebra F Fbar]

  [isAlgClosure : IsAlgClosure F Fbar]

  E : WeierstrassCurve F

  [isElliptic : E.IsElliptic]

namespace EllipticCurveData

attribute [instance] fieldF numberFieldF fieldFbar algebraFbar isAlgClosure isElliptic

end EllipticCurveData
end Iut
end AbcAdaptation.Reference
