import Mathlib.Algebra.Ring.Equiv

/-!
source-id: JT-SCENE1-RING-EQUIV-DICTIONARY-TRANSPORT
scope: generic transport of the four operation dictionaries carried by a
ring equivalence. Dictionary extractors return the exact supplied parameters.
The recast requires an equality proof for each dictionary and preserves the
original underlying equivalence and its full forward function.
This type-instance transport keeps the original function and carriers.
It proves no concrete dictionary equality or paper identity.
Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1.RingEquivDictionaryTransport

universe u v w

variable {R : Type u} {S : Type v}
variable {mR : Mul R} {mS : Mul S} {aR : Add R} {aS : Add S}

def sourceMul (_E : @RingEquiv R S mR mS aR aS) : Mul R := mR

def targetMul (_E : @RingEquiv R S mR mS aR aS) : Mul S := mS

def sourceAdd (_E : @RingEquiv R S mR mS aR aS) : Add R := aR

def targetAdd (_E : @RingEquiv R S mR mS aR aS) : Add S := aS

def expectedSourceMul {P : (@RingEquiv R S mR mS aR aS) → Sort w}
    (_k : (E : @RingEquiv R S mR mS aR aS) → P E) : Mul R := mR

def expectedTargetMul {P : (@RingEquiv R S mR mS aR aS) → Sort w}
    (_k : (E : @RingEquiv R S mR mS aR aS) → P E) : Mul S := mS

def expectedSourceAdd {P : (@RingEquiv R S mR mS aR aS) → Sort w}
    (_k : (E : @RingEquiv R S mR mS aR aS) → P E) : Add R := aR

def expectedTargetAdd {P : (@RingEquiv R S mR mS aR aS) → Sort w}
    (_k : (E : @RingEquiv R S mR mS aR aS) → P E) : Add S := aS

variable {mR' : Mul R} {mS' : Mul S} {aR' : Add R} {aS' : Add S}

def recast (E : @RingEquiv R S mR mS aR aS)
    (hmR : mR = mR') (hmS : mS = mS')
    (haR : aR = aR') (haS : aS = aS') :
    @RingEquiv R S mR' mS' aR' aS' := by
  cases hmR
  cases hmS
  cases haR
  cases haS
  exact E

theorem recast_toEquiv (E : @RingEquiv R S mR mS aR aS)
    (hmR : mR = mR') (hmS : mS = mS')
    (haR : aR = aR') (haS : aS = aS') :
    @RingEquiv.toEquiv R S mR' mS' aR' aS'
        (recast E hmR hmS haR haS) =
      @RingEquiv.toEquiv R S mR mS aR aS E := by
  cases hmR
  cases hmS
  cases haR
  cases haS
  rfl

theorem recast_toFun (E : @RingEquiv R S mR mS aR aS)
    (hmR : mR = mR') (hmS : mS = mS')
    (haR : aR = aR') (haS : aS = aS') :
    @Equiv.toFun R S
        (@RingEquiv.toEquiv R S mR' mS' aR' aS'
          (recast E hmR hmS haR haS)) =
      @Equiv.toFun R S (@RingEquiv.toEquiv R S mR mS aR aS E) := by
  cases hmR
  cases hmS
  cases haR
  cases haS
  rfl

end JoshiTeich.Act1Scene1.RingEquivDictionaryTransport
