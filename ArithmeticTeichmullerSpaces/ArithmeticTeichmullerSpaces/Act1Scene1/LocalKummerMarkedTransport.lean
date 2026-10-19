import ArithmeticTeichmullerSpaces.Act1Scene1.ContinuousH1Transport
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerCoefficientChange

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-MARKED-TRANSPORT
source: Joshi I pr:galois-cohomology-and-teich and cor:collation-classes
(1609--1643); II.5 pr:arith-isom-gal-cohom/pr:collation-principle (1585--1625).
fidelity: a topological isomorphism of the actual Krull Galois groups that
preserves their actual cyclotomic characters produces integral and rational
continuous H1 equivalences. Tate coefficients come from the original bases;
integral-to-rational coefficient change commutes with transport. Collation
uses images under these marked maps, not arbitrary H1 equivalences.
Holomorphoid/anabelomorphism producers, H1_e/BK and log compatibility remain open.
Original proofs; no reference copy or new Core assumptions.
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport
open scoped Topology
universe u w v
noncomputable section
variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
variable {L : Type w} [Field L] {Ξ : Type v} [Field Ξ] [Algebra L Ξ]
variable [Algebra.IsIntegral L Ξ] [CharZero Ξ] [IsAlgClosed Ξ]
variable (p : ℕ) [Fact p.Prime]

/-- This is the group and cyclotomic part of the source marking, before H1. -/
structure Marking where
  groupIso : (Ξ ≃ₐ[L] Ξ) ≃ₜ* (Ω ≃ₐ[K] Ω)
  character_eq : ∀ σ, Cyclotomic.character (K := K) (Ω := Ω) p (groupIso σ) =
    Cyclotomic.character (K := L) (Ω := Ξ) p σ

namespace Marking
variable {p} (m : Marking (K := K) (Ω := Ω) (L := L) (Ξ := Ξ) p)

def coefficientIso (_m : Marking (K := K) (Ω := Ω) (L := L) (Ξ := Ξ) p) : Additive (cyclotomicTateGroup p Ω) ≃L[ℤ_[p]]
    Additive (cyclotomicTateGroup p Ξ) :=
  (TateBasis.equiv (p := p) (Ω := Ω)).symm.trans (TateBasis.equiv (p := p) (Ω := Ξ))

theorem coefficientIso_coordinate (x : Additive (cyclotomicTateGroup p Ω)) :
    (TateBasis.equiv (p := p) (Ω := Ξ)).symm (m.coefficientIso x) =
      (TateBasis.equiv (p := p) (Ω := Ω)).symm x :=
  (TateBasis.equiv (p := p) (Ω := Ξ)).symm_apply_apply _

theorem coefficientIso_equivariant (σ : Ξ ≃ₐ[L] Ξ)
    (x : Additive (cyclotomicTateGroup p Ω)) :
    m.coefficientIso (padicTateRepresentation p (m.groupIso σ) x) =
      padicTateRepresentation p σ (m.coefficientIso x) := by
  apply (TateBasis.equiv (p := p) (Ω := Ξ)).symm.injective
  rw [m.coefficientIso_coordinate, Cyclotomic.coordinate_action_character,
    Cyclotomic.coordinate_action_character, m.coefficientIso_coordinate, m.character_eq]

def integralMarking : ContinuousH1Transport.Marking
    (padicTateTopRep (K := K) (Ω := Ω) p) (padicTateTopRep (K := L) (Ω := Ξ) p) where
  groupIso := m.groupIso
  coefficientIso := m.coefficientIso
  equivariant := m.coefficientIso_equivariant

def rationalMarking : ContinuousH1Transport.Marking
    (Rational.topRep (K := K) (Ω := Ω) p) (Rational.topRep (K := L) (Ω := Ξ) p) where
  groupIso := m.groupIso
  coefficientIso := ContinuousLinearEquiv.refl ℚ_[p] (ULift.{v} ℚ_[p])
  equivariant σ q := by
    apply ULift.ext
    change Rational.representation p (m.groupIso σ) q.down =
      Rational.representation (K := L) (Ω := Ξ) p σ q.down
    rw [Rational.representation_apply, Rational.representation_apply, m.character_eq]

def integralH1 : continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p) ≃L[ℤ_[p]]
    continuousCohomology 1 (padicTateTopRep (K := L) (Ω := Ξ) p) := m.integralMarking.h1Equiv

def rationalH1 : continuousCohomology 1 (Rational.topRep (K := K) (Ω := Ω) p) ≃L[ℚ_[p]]
    continuousCohomology 1 (Rational.topRep (K := L) (Ω := Ξ) p) := m.rationalMarking.h1Equiv

theorem coefficient_change (x : padicTateTopRep (K := K) (Ω := Ω) p) :
    Rational.integralCoefficient (K := L) (Ω := Ξ) p (m.coefficientIso x) =
      Rational.integralCoefficient (K := K) (Ω := Ω) p x := by
  apply ULift.ext
  change ((TateBasis.equiv (p := p) (Ω := Ξ)).symm (m.coefficientIso x) : ℚ_[p]) =
    ((TateBasis.equiv (p := p) (Ω := Ω)).symm x : ℚ_[p])
  exact congrArg (fun r : ℤ_[p] => (r : ℚ_[p])) (m.coefficientIso_coordinate x)

theorem rationalH1_standardMap
    (x : continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p)) :
    m.rationalH1 (Rational.standardMap p x) =
      Rational.standardMap p (m.integralH1 x) := by
  obtain ⟨f, hf, rfl⟩ := ContinuousH1Recognition.classOf_surjective _ x
  change m.rationalMarking.h1Equiv
    (ContinuousH1Semilinear.map _ _ (Rational.integralCoefficient p)
      (Rational.integralCoefficient_equivariant p) (ContinuousH1Homogeneous.classOf _ f hf)) = _
  rw [ContinuousH1Semilinear.map_classOf, m.rationalMarking.h1Equiv_classOf]
  change _ = Rational.standardMap p
    (m.integralMarking.h1Equiv (ContinuousH1Homogeneous.classOf _ f hf))
  rw [m.integralMarking.h1Equiv_classOf, Rational.standardMap,
    ContinuousH1Semilinear.map_classOf]
  congr 1
  ext σ
  exact (m.coefficient_change (f (m.groupIso σ))).symm

/-- Transported cocycles use the original inverse-limit Tate coefficient group. -/
def cocycle (f : continuousCocycles (K := K) (Ω := Ω) p) :
    continuousCocycles (K := L) (Ω := Ξ) p :=
  ⟨⟨fun σ => (m.coefficientIso (Additive.ofMul (f.1 (m.groupIso σ)))).toMul,
    continuous_toMul.comp (m.integralMarking.cochain (padicAdditiveCocycle p f)).continuous⟩,
    fun σ τ => congrArg Additive.toMul
      (m.integralMarking.cochain_law (padicAdditiveCocycle p f) (padicAdditiveCocycle_law p f) σ τ)⟩

theorem integralH1_classOfCocycle (f : continuousCocycles (K := K) (Ω := Ω) p) :
    m.integralH1 (padicClassOfCocycle p f) = padicClassOfCocycle p (m.cocycle f) :=
  m.integralMarking.h1Equiv_classOf _ _

theorem rationalH1_classOfCocycle (f : continuousCocycles (K := K) (Ω := Ω) p) :
    m.rationalH1 (Rational.classOfCocycle p f) = Rational.classOfCocycle p (m.cocycle f) := by
  rw [← Rational.standardMap_classOfCocycle, m.rationalH1_standardMap,
    m.integralH1_classOfCocycle, Rational.standardMap_classOfCocycle]

end Marking

def rationalCollation
    (S : Set (continuousCohomology 1 (Rational.topRep (K := K) (Ω := Ω) p))) :
    Set (continuousCohomology 1 (Rational.topRep (K := L) (Ω := Ξ) p)) :=
  ⋃ m : Marking (K := K) (Ω := Ω) (L := L) (Ξ := Ξ) p, m.rationalH1 '' S

theorem mem_rationalCollation_iff
    (S : Set (continuousCohomology 1 (Rational.topRep (K := K) (Ω := Ω) p)))
    (y : continuousCohomology 1 (Rational.topRep (K := L) (Ω := Ξ) p)) :
    y ∈ rationalCollation p S ↔
      ∃ (m : Marking (K := K) (Ω := Ω) (L := L) (Ξ := Ξ) p), ∃ x ∈ S, m.rationalH1 x = y := by
  simp only [rationalCollation, Set.mem_iUnion, Set.mem_image]

def integralCollation
    (S : Set (continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p))) :
    Set (continuousCohomology 1 (padicTateTopRep (K := L) (Ω := Ξ) p)) :=
  ⋃ m : Marking (K := K) (Ω := Ω) (L := L) (Ξ := Ξ) p, m.integralH1 '' S

theorem rationalization_collation
    (S : Set (continuousCohomology 1 (padicTateTopRep (K := K) (Ω := Ω) p))) :
    Rational.standardMap (K := L) (Ω := Ξ) p '' integralCollation p S =
      rationalCollation p (Rational.standardMap (K := K) (Ω := Ω) p '' S) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨m, x, hx, rfl⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨m, Rational.standardMap p x, ⟨x, hx, rfl⟩,
      m.rationalH1_standardMap x⟩
  · intro y hy
    obtain ⟨m, z, ⟨x, hx, rfl⟩, rfl⟩ := (mem_rationalCollation_iff p _ y).mp hy
    exact ⟨m.integralH1 x, Set.mem_iUnion.mpr ⟨m, x, hx, rfl⟩,
      (m.rationalH1_standardMap x).symm⟩

end
end JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport
