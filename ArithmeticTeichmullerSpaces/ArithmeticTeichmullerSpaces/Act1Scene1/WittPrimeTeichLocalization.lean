import ArithmeticTeichmullerSpaces.Act1Scene1.WittRingEquiv

/-!
source-id: JT-SCENE1-WITT-PRIME-TEICH-LOCALIZATION
source: Joshi II `se:ff-rings`, the algebraic localization of W(O_F)
obtained by inverting p and a nonzero contracting Teichmuller element.
fidelity: transports the original two-element localization through a
coefficient-ring equivalence that maps the specified elements to each other.
The algebraMap formula retains the original Witt map. The generic result
does not require a norm or a comparison certificate for completed rings.
Original proofs; no reference implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.WittPrimeTeichLocalization

noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {R S : Type*} [CommRing R] [CommRing S]

def denominator (s : R) : WittVector p R :=
  (p : WittVector p R) * WittVector.teichmuller p s

abbrev Ring (s : R) := Localization.Away (denominator p s)

theorem map_denominator (e : R ≃+* S) (r : R) (s : S) (h : e r = s) :
    WittRingEquiv.mapEquiv p e (denominator p r) = denominator p s := by
  change WittRingEquiv.mapEquiv p e
    ((p : WittVector p R) * WittVector.teichmuller p r) =
      (p : WittVector p S) * WittVector.teichmuller p s
  rw [map_mul, map_natCast, WittRingEquiv.mapEquiv_teichmuller, h]

def equiv (e : R ≃+* S) (r : R) (s : S) (h : e r = s) :
    Ring p r ≃+* Ring p s :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (denominator p r))
    (T := Submonoid.powers (denominator p s))
    _ _ (WittRingEquiv.mapEquiv p e) (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers (map_denominator p e r s h))

theorem equiv_algebraMap (e : R ≃+* S) (r : R) (s : S) (h : e r = s)
    (x : WittVector p R) :
    equiv p e r s h (algebraMap _ (Ring p r) x) =
      algebraMap _ (Ring p s) (WittRingEquiv.mapEquiv p e x) := by
  simp only [equiv, IsLocalization.ringEquivOfRingEquiv_eq]

theorem equiv_presentation (e : R ≃+* S) (r : R) (s : S) (h : e r = s)
    (x : Ring p r) (m : ℕ) (a : WittVector p R)
    (hx : x * algebraMap _ (Ring p r) (denominator p r) ^ m =
      algebraMap _ (Ring p r) a) :
    equiv p e r s h x * algebraMap _ (Ring p s) (denominator p s) ^ m =
      algebraMap _ (Ring p s) (WittRingEquiv.mapEquiv p e a) := by
  have hmap := congrArg (equiv p e r s h) hx
  rw [map_mul, map_pow,
    equiv_algebraMap p e r s h (denominator p r),
    map_denominator p e r s h,
    equiv_algebraMap p e r s h a] at hmap
  exact hmap

end
end JoshiTeich.Act1Scene1.WittPrimeTeichLocalization
