import ArithmeticTeichmullerSpaces.Act1Scene1.WittPrimeTeichLocalization
import ArithmeticTeichmullerSpaces.Act1Scene1.WittFrobeniusTeichmullerRigidity

/-!
source-id: JT-SCENE1-WITT-PRIME-TEICH-FROBENIUS
source: Joshi II `se:ff-rings`, Frobenius on the localization of integral
Witt vectors at p and a Teichmuller element; Mathlib localization universal
property and Witt Frobenius naturality.
fidelity: constructs the forward Witt Frobenius on the original
WittPrimeTeichLocalization.Ring and proves its inclusion law, uniqueness,
and naturality under the original coefficient-induced localization
equivalence. The denominator and carriers are unchanged. Characteristic p
suffices; no perfectness, norm law, or comparison certificate is needed.
Original proofs; no reference implementation copied.
boundary: forward algebraic Frobenius only; invertibility, completion and
paper B, period and BK identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.WittPrimeTeichFrobenius

open WittPrimeTeichLocalization
noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable {R S : Type*} [CommRing R] [CommRing S]

theorem prime_isUnit (r : R) :
    IsUnit (algebraMap (WittVector p R) (Ring p r) p) := by
  apply isUnit_of_mul_isUnit_left
    (y := algebraMap (WittVector p R) (Ring p r) (WittVector.teichmuller p r))
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (denominator p r)

theorem teich_isUnit (r : R) :
    IsUnit (algebraMap (WittVector p R) (Ring p r) (WittVector.teichmuller p r)) := by
  apply isUnit_of_mul_isUnit_right
    (x := algebraMap (WittVector p R) (Ring p r) p)
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (denominator p r)

variable [CharP R p]

theorem frobenius_denominator_isUnit (r : R) :
    IsUnit
      (((algebraMap (WittVector p R) (Ring p r)).comp WittVector.frobenius)
        (denominator p r)) := by
  change IsUnit
    (algebraMap (WittVector p R) (Ring p r)
      (WittVector.frobenius
        ((p : WittVector p R) * WittVector.teichmuller p r)))
  rw [map_mul, map_natCast,
    WittFrobeniusTeichmullerRigidity.frobenius_teichmuller,
    map_mul, map_pow]
  exact (prime_isUnit p r).mul ((teich_isUnit p r).pow p)

def hom (r : R) : Ring p r →+* Ring p r :=
  IsLocalization.Away.lift (denominator p r) (frobenius_denominator_isUnit p r)

theorem hom_inclusion (r : R) (a : WittVector p R) :
    hom p r (algebraMap (WittVector p R) (Ring p r) a) =
      algebraMap (WittVector p R) (Ring p r) (WittVector.frobenius a) :=
  IsLocalization.Away.lift_eq _ _ a

theorem hom_unique (r : R) (F : Ring p r →+* Ring p r)
    (hF : ∀ a : WittVector p R,
      F (algebraMap (WittVector p R) (Ring p r) a) =
        algebraMap (WittVector p R) (Ring p r) (WittVector.frobenius a)) :
    F = hom p r := by
  apply IsLocalization.ringHom_ext (M := Submonoid.powers (denominator p r))
  apply RingHom.ext
  intro a
  exact (hF a).trans (hom_inclusion p r a).symm

variable [CharP S p]

theorem equiv_hom (e : R ≃+* S) (r : R) (s : S) (h : e r = s)
    (x : Ring p r) :
    equiv p e r s h (hom p r x) = hom p s (equiv p e r s h x) := by
  have he : (equiv p e r s h).toRingHom.comp (hom p r) =
      (hom p s).comp (equiv p e r s h).toRingHom := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers (denominator p r))
    apply RingHom.ext
    intro a
    change equiv p e r s h
        (hom p r (algebraMap (WittVector p R) (Ring p r) a)) =
      hom p s (equiv p e r s h (algebraMap (WittVector p R) (Ring p r) a))
    rw [hom_inclusion, equiv_algebraMap, equiv_algebraMap, hom_inclusion]
    exact congrArg (algebraMap (WittVector p S) (Ring p s))
      (WittRingEquiv.mapEquiv_frobenius p e a)
  exact RingHom.congr_fun he x

end
end JoshiTeich.Act1Scene1.WittPrimeTeichFrobenius
