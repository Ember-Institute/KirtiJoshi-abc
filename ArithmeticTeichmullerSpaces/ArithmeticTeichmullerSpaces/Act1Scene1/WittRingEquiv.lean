import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.RingTheory.WittVector.Frobenius
import Mathlib.RingTheory.Localization.Algebra

/-!
source-id: JT-SCENE1-WITT-RING-EQUIV
source: Joshi II `se:ff-rings`, functoriality of the integral Witt ring;
Mathlib WittVector.map and its injectivity/surjectivity theorems.
fidelity: lifts a ring equivalence to the original Witt-vector carriers,
with coefficient, Teichmuller, and characteristic-p Frobenius formulas.
The generic definition fixes the coefficient-ring instances before a
concrete geometric comparison is supplied. Original proofs; R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.WittRingEquiv

noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {R S : Type*} [CommRing R] [CommRing S]

def mapEquiv (e : R ≃+* S) : WittVector p R ≃+* WittVector p S :=
  RingEquiv.ofBijective (WittVector.map e.toRingHom)
    ⟨WittVector.map_injective _ e.injective, WittVector.map_surjective _ e.surjective⟩

theorem mapEquiv_apply (e : R ≃+* S) (x : WittVector p R) :
    mapEquiv p e x = WittVector.map e.toRingHom x := rfl

theorem mapEquiv_coeff (e : R ≃+* S) (x : WittVector p R) (n : ℕ) :
    (mapEquiv p e x).coeff n = e (x.coeff n) := rfl

theorem mapEquiv_teichmuller (e : R ≃+* S) (r : R) :
    mapEquiv p e (WittVector.teichmuller p r) = WittVector.teichmuller p (e r) :=
  WittVector.map_teichmuller p e.toRingHom r

theorem mapEquiv_frobenius [CharP R p] [CharP S p]
    (e : R ≃+* S) (x : WittVector p R) :
    mapEquiv p e (WittVector.frobenius x) = WittVector.frobenius (mapEquiv p e x) := by
  apply WittVector.ext
  intro n
  simp only [mapEquiv_coeff, WittVector.coeff_frobenius_charP, map_pow]

def invertPrimeEquiv (e : R ≃+* S) :
    Localization.Away (p : WittVector p R) ≃+* Localization.Away (p : WittVector p S) :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (p : WittVector p R))
    (T := Submonoid.powers (p : WittVector p S))
    _ _ (mapEquiv p e) (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers (map_natCast (mapEquiv p e).toRingHom p))

theorem invertPrimeEquiv_algebraMap (e : R ≃+* S) (x : WittVector p R) :
    invertPrimeEquiv p e (algebraMap _ (Localization.Away (p : WittVector p R)) x) =
      algebraMap _ (Localization.Away (p : WittVector p S)) (mapEquiv p e x) := by
  simp only [invertPrimeEquiv, IsLocalization.ringEquivOfRingEquiv_eq]

end
end JoshiTeich.Act1Scene1.WittRingEquiv
