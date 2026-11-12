import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Mathlib `AddSubgroup.mem_inertia` and
`Ideal.ker_algebraMap_residueField`.
fidelity: inverse precomposition gives the usual action on affine points.
The stabilizer of a point is the inertia subgroup of its kernel. A prime
has a concrete point valued in the algebraic closure of its residue field.
boundary: Scene1/Derived. Consumers must supply the actual ring action;
this module does not assert an orbicurve realization.
-/

namespace JoshiTeich.Act1Scene1.GeometricPointInertia

universe u v w
noncomputable section

variable (G : Type u) (R : Type v) (C : Type w)
variable [Group G] [CommRing R] [CommRing C] [MulSemiringAction G R]

/-- Translate a point by inverse precomposition with the actual ring action. -/
def translatePoint (g : G) (f : R →+* C) : R →+* C :=
  f.comp (MulSemiringAction.toRingHom G R g⁻¹)

@[instance_reducible] def pointAction : MulAction G (R →+* C) where
  smul := translatePoint G R C
  one_smul f := RingHom.ext fun x => by
    change f ((1 : G)⁻¹ • x) = f x
    rw [inv_one, one_smul]
  mul_smul g h f := RingHom.ext fun x => by
    change f ((g * h)⁻¹ • x) = f (h⁻¹ • (g⁻¹ • x))
    rw [mul_inv_rev, mul_smul]

attribute [local instance] pointAction

/-- Fixing an affine point means acting trivially modulo its kernel. -/
theorem mem_stabilizer_iff_inertia (f : R →+* C) (g : G) :
    g ∈ MulAction.stabilizer G f ↔ g ∈ (RingHom.ker f).inertia G := by
  constructor
  · intro hg
    have hi : g⁻¹ ∈ (RingHom.ker f).inertia G := by
      apply AddSubgroup.mem_inertia.mpr
      intro x
      change f (g⁻¹ • x - x) = 0
      rw [map_sub, sub_eq_zero]
      exact RingHom.congr_fun hg x
    have hinv := ((RingHom.ker f).inertia G).inv_mem hi
    simpa only [inv_inv] using hinv
  · intro hg
    apply RingHom.ext
    intro x
    have hi := AddSubgroup.mem_inertia.mp (((RingHom.ker f).inertia G).inv_mem hg) x
    change f (g⁻¹ • x) = f x
    change f (g⁻¹ • x - x) = 0 at hi
    exact sub_eq_zero.mp (by simpa only [map_sub] using hi)

theorem stabilizer_eq_inertia (f : R →+* C) :
    MulAction.stabilizer G f = (RingHom.ker f).inertia G :=
  Subgroup.ext (mem_stabilizer_iff_inertia G R C f)

section ResiduePoint
variable {R}

/-- A concrete geometric point above a prime, with an algebraically closed target. -/
def residueGeometricPoint (P : Ideal R) [P.IsPrime] :
    R →+* AlgebraicClosure P.ResidueField :=
  (algebraMap P.ResidueField (AlgebraicClosure P.ResidueField)).comp
    (algebraMap R P.ResidueField)

theorem ker_residueGeometricPoint (P : Ideal R) [P.IsPrime] :
    RingHom.ker (residueGeometricPoint P) = P := by
  rw [residueGeometricPoint, RingHom.ker_comp_of_injective _
    (algebraMap P.ResidueField (AlgebraicClosure P.ResidueField)).injective,
    Ideal.ker_algebraMap_residueField]

end ResiduePoint
end
end JoshiTeich.Act1Scene1.GeometricPointInertia
