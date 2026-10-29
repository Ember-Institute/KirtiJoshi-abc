import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAnnularExponential

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-ANNULAR-FINITE-COORDINATE-DENSITY
source: Joshi II `se:ff-rings`, annular closures in the period-ring
construction preceding `pr:teichmuller-lift-A`.
fidelity: the annular carrier is the closure of one original bounded
Witt diagonal. Proves its source map has dense range and gives one
original source element approximating any annular element simultaneously
at the base radius and at one chosen auxiliary radius. This is the
finite-coordinate input for a future annular integral representative.
Original proof; no reference code copied.
boundary: Scene1/Derived; finite-coordinate density does not remove
negative p-powers or produce an Ainf representative. The annular carrier
remains distinct from the full common completion. Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittAnnularFiniteCoordinateDensity

open JoshiTeich.Prologue
open InitialThetaWittAnnularExponential
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Radius := InitialThetaWittRhoCompletion.Radius

def sourceInclusion (ρ : Radius) :
    InitialThetaBoundedWittLocalization.Ring D w →+* Carrier D w ρ :=
  (diagonal D w ρ).codRestrict (closedSubring D w ρ)
    (fun y => Subring.le_topologicalClosure _ ⟨y, rfl⟩)

theorem sourceInclusion_apply (ρ : Radius)
    (y : InitialThetaBoundedWittLocalization.Ring D w) :
    evaluate D w ρ ⟨ρ, le_rfl⟩ (sourceInclusion D w ρ y) =
      InitialThetaWittRhoCompletion.inclusion D w ρ y := rfl

theorem evaluate_continuous (ρ : Radius) (s : AnnularRadius ρ) :
    Continuous (evaluate D w ρ s) :=
  (continuous_apply s).comp continuous_subtype_val

theorem sourceInclusion_denseRange (ρ : Radius) :
    DenseRange (sourceInclusion D w ρ) := by
  apply Subtype.dense_iff.mpr
  rw [← Set.range_comp]
  change (closedSubring D w ρ : Set (Product D w ρ)) ⊆
    closure (Set.range (diagonal D w ρ))
  exact Set.Subset.rfl

theorem exists_source_approximation
    (ρ : Radius) (t : AnnularRadius ρ) (x : Carrier D w ρ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ y : InitialThetaBoundedWittLocalization.Ring D w,
      ‖evaluate D w ρ ⟨ρ, le_rfl⟩ (sourceInclusion D w ρ y) -
          evaluate D w ρ ⟨ρ, le_rfl⟩ x‖ < ε ∧
      ‖evaluate D w ρ t (sourceInclusion D w ρ y) - evaluate D w ρ t x‖ < ε := by
  let U : Set (Carrier D w ρ) := {z |
    ‖evaluate D w ρ ⟨ρ, le_rfl⟩ z - evaluate D w ρ ⟨ρ, le_rfl⟩ x‖ < ε ∧
    ‖evaluate D w ρ t z - evaluate D w ρ t x‖ < ε}
  have hopen : IsOpen U :=
    (isOpen_lt ((evaluate_continuous D w ρ ⟨ρ, le_rfl⟩).sub continuous_const).norm continuous_const).inter
      (isOpen_lt ((evaluate_continuous D w ρ t).sub continuous_const).norm continuous_const)
  have hmem : x ∈ U := by
    simp only [U, Set.mem_setOf_eq, sub_self, norm_zero]
    exact ⟨hε, hε⟩
  obtain ⟨y, hy⟩ := (sourceInclusion_denseRange D w ρ).exists_mem_open hopen ⟨x, hmem⟩
  exact ⟨y, hy.1, hy.2⟩

end
end JoshiTeich.Act1Scene1.InitialThetaWittAnnularFiniteCoordinateDensity
