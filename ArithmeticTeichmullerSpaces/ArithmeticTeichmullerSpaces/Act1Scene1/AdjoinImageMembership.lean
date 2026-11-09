import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`.
fidelity: a homomorphism on a generated coordinate algebra lands in a subalgebra
when its generators do. Consumed by the original polynomial-base inclusion.
Original proof; no reference implementation copied.
-/
namespace JoshiTeich.Act1Scene1.AdjoinImageMembership

variable {k Ω C : Type*} [CommSemiring k] [Semiring Ω] [Semiring C]
  [Algebra k Ω] [Algebra k C]

/-- Check the image of a generated algebra on its original generators. -/
theorem image_mem (s : Set Ω) (f : Algebra.adjoin k s →ₐ[k] C)
    (B : Subalgebra k C)
    (hgen : ∀ x (hx : x ∈ s), f ⟨x, Algebra.subset_adjoin hx⟩ ∈ B)
    (a : Algebra.adjoin k s) : f a ∈ B := by
  refine Algebra.adjoin_induction
    (p := fun x hx => f ⟨x, hx⟩ ∈ B) hgen ?_ ?_ ?_ a.property
  · intro r
    change f (algebraMap k (Algebra.adjoin k s) r) ∈ B
    rw [f.commutes]
    exact B.algebraMap_mem r
  · intro x y hx hy hxc hyc
    change f ((⟨x, hx⟩ : Algebra.adjoin k s) + ⟨y, hy⟩) ∈ B
    rw [map_add]
    exact B.add_mem hxc hyc
  · intro x y hx hy hxc hyc
    change f ((⟨x, hx⟩ : Algebra.adjoin k s) * ⟨y, hy⟩) ∈ B
    rw [map_mul]
    exact B.mul_mem hxc hyc

/-- The one-coordinate specialization avoids dependent elimination in consumers. -/
theorem image_mem_singleton (t : Ω)
    (f : Algebra.adjoin k ({t} : Set Ω) →ₐ[k] C) (B : Subalgebra k C)
    (hgen : f ⟨t, Algebra.subset_adjoin (Set.mem_singleton t)⟩ ∈ B)
    (a : Algebra.adjoin k ({t} : Set Ω)) : f a ∈ B := by
  apply image_mem {t} f B ?_ a
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact hgen

end JoshiTeich.Act1Scene1.AdjoinImageMembership
