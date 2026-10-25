import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBoundedWittLocalization
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.Algebra.Rat

/-!
source-id: JT-SCENE1-INITIAL-THETA-BOUNDED-WITT-RATIONAL-SCALARS
source: Joshi II `se:ff-rings`, the bounded period subring with p inverted;
Mathlib WittVector.Compare and WittVector.DiscreteValuationRing.
fidelity: maps the prime-field Witt constants into the actual bounded
localization. Nonzero integer constants are p-powers times units, so
all rational denominators are invertible. Constructs the actual rational
scalar embedding and proves that the original Frobenius fixes it.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; p-adic scalar completion, topological scalar
action, Tate-log and paper B/BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaBoundedWittRationalScalars

open JoshiTeich.Prologue
open InitialThetaBoundedWittLocalization
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def primeWittMap : WittVector (Arithmetic.residueChar w.1) (ZMod (Arithmetic.residueChar w.1)) →+*
    InitialThetaBoundedWittLocalization.Ring D w :=
  (inclusion D w).comp (WittVector.map
    (ZMod.castHom (dvd_refl (Arithmetic.residueChar w.1)) (InitialThetaTiltIntegers.Integers D w)))

theorem intCast_isUnit (n : ℤ) (hn : n ≠ 0) :
    IsUnit (n : InitialThetaBoundedWittLocalization.Ring D w) := by
  let p := Arithmetic.residueChar w.1
  have hnW : (n : WittVector p (ZMod p)) ≠ 0 := by
    intro hz
    let f : WittVector p (ZMod p) →+* PadicInt p := (WittVector.equiv p).toRingHom
    have he : f (n : WittVector p (ZMod p)) = 0 := (congrArg f hz).trans f.map_zero
    exact (Int.cast_ne_zero.mpr hn) ((map_intCast f n).symm.trans he)
  obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' (n : WittVector p (ZMod p)) hnW
  have hpR : IsUnit (p : InitialThetaBoundedWittLocalization.Ring D w) := by
    simpa only [map_natCast] using prime_isUnit D w
  have hunit : IsUnit (primeWittMap D w ((p : WittVector p (ZMod p)) ^ m * u)) := by
    rw [map_mul, map_pow, map_natCast]
    exact (hpR.pow m).mul (u.isUnit.map (primeWittMap D w))
  simpa only [← hu, map_intCast] using hunit

def rationalMap : ℚ →+* InitialThetaBoundedWittLocalization.Ring D w :=
  IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ)
    (g := Int.castRingHom (InitialThetaBoundedWittLocalization.Ring D w))
    (fun y => intCast_isUnit D w y.val (mem_nonZeroDivisors_iff_ne_zero.mp y.property))

instance boundedRatAlgebra : Algebra ℚ (InitialThetaBoundedWittLocalization.Ring D w) :=
  (rationalMap D w).toAlgebra

theorem rationalMap_injective : Function.Injective (rationalMap D w) :=
  (rationalMap D w).injective

theorem rationalMap_intCast (n : ℤ) : rationalMap D w (n : ℚ) = n :=
  map_intCast _ n

theorem frobenius_rational (q : ℚ) :
    frobeniusEquiv D w (rationalMap D w q) = rationalMap D w q :=
  RingHom.map_rat_algebraMap (frobeniusEquiv D w).toRingHom q

end
end JoshiTeich.Act1Scene1.InitialThetaBoundedWittRationalScalars
