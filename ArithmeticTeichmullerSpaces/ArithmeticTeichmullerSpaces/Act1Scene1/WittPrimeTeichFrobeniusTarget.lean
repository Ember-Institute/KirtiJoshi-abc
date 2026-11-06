import ArithmeticTeichmullerSpaces.Act1Scene1.WittPrimeTeichFrobenius

/-!
source-id: JT-SCENE1-WITT-PRIME-TEICH-FROBENIUS-TARGET
source: Joshi II `se:ff-rings`, functorial Frobenius on the localization
of integral Witt vectors at p and a Teichmuller element.
fidelity: specializes generic Frobenius naturality to a target element,
with its source element computed by the inverse coefficient equivalence.
The element-image equality is discharged inside the generic statement.
The original localization equivalence, Frobenius homomorphisms, denominator
and carriers are retained. No norm, perfectness or comparison certificate
is assumed. Original proof; no reference implementation copied.
boundary: generic algebraic naturality only; concrete comparisons,
completion and paper B, period and BK identities remain separate.
-/

namespace JoshiTeich.Act1Scene1.WittPrimeTeichFrobenius

open WittPrimeTeichLocalization
noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable {R S : Type*} [CommRing R] [CommRing S]
variable [CharP R p] [CharP S p]

theorem equiv_hom_target (e : R ≃+* S) (s : S)
    (x : Ring p (e.symm s)) :
    equiv p e (e.symm s) s (e.apply_symm_apply s)
        (hom p (e.symm s) x) =
      hom p s (equiv p e (e.symm s) s (e.apply_symm_apply s) x) :=
  equiv_hom p e (e.symm s) s (e.apply_symm_apply s) x

end
end JoshiTeich.Act1Scene1.WittPrimeTeichFrobenius
