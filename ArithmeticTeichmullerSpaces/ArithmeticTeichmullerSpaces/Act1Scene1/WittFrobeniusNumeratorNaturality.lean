import ArithmeticTeichmullerSpaces.Act1Scene1.WittRingEquiv

/-!
source-id: JT-SCENE1-WITT-FROBENIUS-NUMERATOR-NATURALITY
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, Frobenius
on bounded Witt numerator presentations.
fidelity: transports the explicit numerator
((p : WittVector p R) ^ (p - 1)) ^ m * WittVector.frobenius a
through the original coefficient-induced Witt equivalence. The proof uses
its preservation of products, powers and natural-number scalars, together
with the existing Witt Frobenius naturality theorem. The equivalence is the
first explicit argument; all Witt carriers and functions are unchanged.
Only primality, commutative rings and characteristic p are required. No
presentation definition or additional comparison assumption is introduced.
Original proof; no reference implementation copied.
boundary: Scene1/Derived; numerator naturality only. Localization, completion
and the paper B, period and BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.WittFrobeniusNumeratorNaturality

noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {R S : Type*} [CommRing R] [CommRing S]
variable [CharP R p] [CharP S p]

theorem map_numerator (e : R ≃+* S) (m : ℕ) (a : WittVector p R) :
    WittRingEquiv.mapEquiv p e
        (((p : WittVector p R) ^ (p - 1)) ^ m * WittVector.frobenius a) =
      ((p : WittVector p S) ^ (p - 1)) ^ m *
        WittVector.frobenius (WittRingEquiv.mapEquiv p e a) := by
  rw [map_mul, map_pow, map_pow, map_natCast,
    WittRingEquiv.mapEquiv_frobenius]

end
end JoshiTeich.Act1Scene1.WittFrobeniusNumeratorNaturality
