import ArithmeticTeichmullerSpaces.Act1Scene1.GaloisClosureTransport
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
source-id: JT-SCENE1-EMBEDDED-ALGEBRAIC-CLOSURE
source: Joshi I def:untilt-galois (1470--1498) and preferred Kummer closures
(1588--1632); Mathlib relative algebraicClosure and IsAlgClosure.equiv.
fidelity: constructs the preferred algebraic closure inside a given
algebraically closed field from its base embedding. Its image is exactly
all elements algebraic over the embedded base. The closure comparison
produces the original Krull Galois group marking and its intertwining law.
No action on the whole ambient field or tempered marking is asserted.
Original proofs; no reference copy or new Core assumptions.
-/
namespace JoshiTeich.Act1Scene1.EmbeddedAlgebraicClosure
universe u
noncomputable section
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]

/-- The relative algebraic closure uses the specified base algebra. -/
abbrev Carrier := ↥(algebraicClosure k Ω)

def inclusion : Carrier k Ω →+* Ω := (algebraicClosure k Ω).val.toRingHom

theorem inclusion_injective : Function.Injective (inclusion k Ω) := (inclusion k Ω).injective

theorem inclusion_algebraMap (a : k) :
    inclusion k Ω (algebraMap k (Carrier k Ω) a) = algebraMap k Ω a := rfl

theorem mem_inclusion_range_iff (x : Ω) :
    x ∈ (inclusion k Ω).range ↔ IsAlgebraic k x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact mem_algebraicClosure_iff.mp y.2
  · intro hx
    exact ⟨⟨x, mem_algebraicClosure_iff.mpr hx⟩, rfl⟩

variable [IsAlgClosed Ω]

def equiv : AlgebraicClosure k ≃ₐ[k] Carrier k Ω :=
  IsAlgClosure.equiv k (AlgebraicClosure k) (Carrier k Ω)

def embedding : AlgebraicClosure k →+* Ω := (inclusion k Ω).comp (equiv k Ω).toRingHom

theorem embedding_algebraMap (a : k) :
    embedding k Ω (algebraMap k (AlgebraicClosure k) a) = algebraMap k Ω a := by
  change inclusion k Ω (equiv k Ω (algebraMap k (AlgebraicClosure k) a)) = _
  rw [(equiv k Ω).commutes, inclusion_algebraMap]

theorem embedding_range : (embedding k Ω).range = (inclusion k Ω).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨equiv k Ω y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨(equiv k Ω).symm y, congrArg (inclusion k Ω) ((equiv k Ω).apply_symm_apply y)⟩

theorem mem_embedding_range_iff (x : Ω) :
    x ∈ (embedding k Ω).range ↔ IsAlgebraic k x := by
  rw [embedding_range]
  exact mem_inclusion_range_iff k Ω x

def groupIso : (Carrier k Ω ≃ₐ[k] Carrier k Ω) ≃ₜ* (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :=
  GaloisClosureTransport.groupIso (equiv k Ω)

theorem intertwine (σ : Carrier k Ω ≃ₐ[k] Carrier k Ω) (x : AlgebraicClosure k) :
    embedding k Ω (groupIso k Ω σ x) = inclusion k Ω (σ (equiv k Ω x)) :=
  congrArg (inclusion k Ω) (GaloisClosureTransport.intertwine (equiv k Ω) σ x)

end
end JoshiTeich.Act1Scene1.EmbeddedAlgebraicClosure
