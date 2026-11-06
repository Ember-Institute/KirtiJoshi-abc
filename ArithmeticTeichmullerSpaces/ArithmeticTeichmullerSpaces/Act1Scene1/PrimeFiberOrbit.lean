import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.Order.Setoid.Basic

/-!
source-id: JT-SCENE1-PRIME-FIBER-ORBIT-QUOTIENT-20261107
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
Mathlib's transitivity of a finite invariant ring action on primes above a prime.
fidelity: restriction of prime fibers is invariant under the actual ring action,
and two primes have the same restriction exactly when they lie in one orbit.
A surjective restriction map therefore identifies the lower fiber with the
orbit quotient of the upper fiber. The map remains the supplied actual map,
whose underlying ideals are required to be literal contractions.
Original proofs; no reference implementation copied.
boundary: generic prime-fiber algebra; the actual ring action and invariant
ring law must be proved at each application. No torsion-cusp identification,
distinguished cusp, or orbicurve realization is asserted.
-/

namespace JoshiTeich.Act1Scene1.PrimeFiberOrbit

open scoped Classical Pointwise
noncomputable section

variable {R A B G : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
  [SMulCommClass G R B]

variable (p : Ideal R) (f : p.primesOver B → p.primesOver A)
  (hcoe : ∀ q, (f q).1 = q.1.under A)

include hcoe

/-- The original contraction map is constant on actual prime orbits. -/
theorem map_smul (g : G) (q : p.primesOver B) : f (g • q) = f q := by
  apply Subtype.ext
  rw [hcoe, hcoe, Ideal.coe_smul_primesOver, Ideal.under_smul]

/-- Contraction fibers are exactly the orbits of the actual finite Galois action. -/
theorem map_eq_iff_exists_smul (q₁ q₂ : p.primesOver B) :
    f q₁ = f q₂ ↔ ∃ g : G, g • q₁ = q₂ := by
  constructor
  · intro h
    have : q₁.1.IsPrime := q₁.2.1
    have : q₂.1.IsPrime := q₂.2.1
    have hUnder : q₁.1.under A = q₂.1.under A :=
      (hcoe q₁).symm.trans ((congrArg Subtype.val h).trans (hcoe q₂))
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G q₁.1 q₂.1 hUnder
    exact ⟨g, Subtype.ext hg.symm⟩
  · rintro ⟨g, hg⟩
    exact (map_smul p f hcoe g q₁).symm.trans (congrArg f hg)

/-- The orbit relation equals the kernel relation of the actual contraction map. -/
theorem orbitRel_iff_map_eq (q₁ q₂ : p.primesOver B) :
    MulAction.orbitRel G (p.primesOver B) q₁ q₂ ↔ f q₁ = f q₂ := by
  change (∃ g : G, g • q₂ = q₁) ↔ f q₁ = f q₂
  exact (map_eq_iff_exists_smul p f hcoe q₂ q₁).symm.trans eq_comm

/-- The lower fiber is the actual upper prime fiber modulo its Galois action. -/
def orbitQuotientEquiv (hsurj : Function.Surjective f) :
    MulAction.orbitRel.Quotient G (p.primesOver B) ≃ p.primesOver A :=
  (Quotient.congrRight
    (r := MulAction.orbitRel G (p.primesOver B)) (r' := Setoid.ker f)
    (orbitRel_iff_map_eq p f hcoe)).trans
      (Setoid.quotientKerEquivOfSurjective f hsurj)

theorem orbitQuotientEquiv_mk (hsurj : Function.Surjective f) (q : p.primesOver B) :
    orbitQuotientEquiv p f hcoe hsurj
      (Quotient.mk (MulAction.orbitRel G (p.primesOver B)) q) = f q := rfl

end
end JoshiTeich.Act1Scene1.PrimeFiberOrbit
