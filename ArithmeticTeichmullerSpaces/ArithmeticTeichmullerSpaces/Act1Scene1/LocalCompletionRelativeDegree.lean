import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionDegree
import ArithmeticTeichmullerSpaces.Act1Scene1.IutCompletionSource
import Mathlib.LinearAlgebra.Dimension.Free

/-!
source-id: JT-SCENE1-LOCAL-COMPLETION-RELATIVE-DEGREE
source: actual continuous completion embedding, density of rational numbers
in the p-adics, absolute completion degrees and the scalar-tower dimension law.
fidelity: constructs the actual relative completion algebra and proves that
its dimension is the relative ramification/inertia product. Its inverse is
the ratio of the two absolute local degrees, as required by Joshi III eq:weights.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion

open NumberField
open JoshiTeich.Prologue.Arithmetic
universe u
noncomputable section
variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {w : FinitePlace K} {v : FinitePlace L}
variable (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)

/-- The actual relative completion algebra uses the proved completion embedding. -/
def relativeAlgebra : Algebra (completionAt K w) (completionAt L v) :=
  (iutEmbedCompletion hvw).toAlgebra

section Padic
variable {p : ℕ} [Fact p.Prime] (hw : residueChar w = p)

theorem embedCompletion_padicEmb (x : ℚ_[p]) :
    iutEmbedCompletion hvw (padicEmb hw x) =
      padicEmb ((residueChar_eq_of_liesOver hvw).trans hw) x := by
  have he := DenseRange.equalizer (Padic.denseRange_ratCast p)
    ((iutContinuousEmbedCompletion hvw).comp (continuous_padicEmb hw))
    (continuous_padicEmb ((residueChar_eq_of_liesOver hvw).trans hw)) (by
      funext q
      change iutEmbedCompletion hvw (padicEmb hw (q : ℚ_[p])) =
        padicEmb ((residueChar_eq_of_liesOver hvw).trans hw) (q : ℚ_[p])
      rw [padicEmb_ratCast, padicEmb_ratCast]
      change iutEmbedCompletion hvw (FinitePlace.embedding w.maximalIdeal (q : K)) =
        FinitePlace.embedding v.maximalIdeal (q : L)
      rw [iutEmbedCompletion_embedding, map_ratCast])
  exact congrFun he x

theorem relativeAlgebra_padicTower :
    letI := padicAlgebra hw
    letI := padicAlgebra ((residueChar_eq_of_liesOver hvw).trans hw)
    letI := relativeAlgebra hvw
    IsScalarTower ℚ_[p] (completionAt K w) (completionAt L v) := by
  letI := padicAlgebra hw
  letI := padicAlgebra ((residueChar_eq_of_liesOver hvw).trans hw)
  letI := relativeAlgebra hvw
  exact IsScalarTower.of_algebraMap_eq fun x => (embedCompletion_padicEmb hvw hw x).symm

end Padic

theorem finite_relativeAlgebra :
    letI := relativeAlgebra hvw
    Module.Finite (completionAt K w) (completionAt L v) := by
  let p := residueChar w
  letI : Fact p.Prime := ⟨residueChar_prime w⟩
  let hv : residueChar v = p := residueChar_eq_of_liesOver hvw
  letI := padicAlgebra (show residueChar w = p from rfl)
  letI := padicAlgebra hv
  letI := relativeAlgebra hvw
  letI : IsScalarTower ℚ_[p] (completionAt K w) (completionAt L v) :=
    relativeAlgebra_padicTower hvw rfl
  letI : Module.Finite ℚ_[p] (completionAt L v) := finite_padicAlgebra hv
  exact Module.Finite.of_restrictScalars_finite ℚ_[p] (completionAt K w) (completionAt L v)

theorem finrank_relativeAlgebra_eq_ramification_inertia :
    letI := relativeAlgebra hvw
    Module.finrank (completionAt K w) (completionAt L v) = relRamIdx v w * relInertDeg v w := by
  let p := residueChar w
  letI : Fact p.Prime := ⟨residueChar_prime w⟩
  let hv : residueChar v = p := residueChar_eq_of_liesOver hvw
  letI := padicAlgebra (show residueChar w = p from rfl)
  letI := padicAlgebra hv
  letI := relativeAlgebra hvw
  letI : IsScalarTower ℚ_[p] (completionAt K w) (completionAt L v) :=
    relativeAlgebra_padicTower hvw rfl
  have hd := Module.finrank_mul_finrank ℚ_[p] (completionAt K w) (completionAt L v)
  rw [finrank_padic_eq_localDeg w rfl, finrank_padic_eq_localDeg v hv] at hd
  exact Nat.eq_of_mul_eq_mul_left (localDeg_pos w) (hd.trans (localDeg_eq_mul hvw))

theorem inverse_relativeFinrank_eq_localDeg_ratio :
    letI := relativeAlgebra hvw
    1 / (Module.finrank (completionAt K w) (completionAt L v) : ℝ) =
      (localDeg w : ℝ) / localDeg v := by
  letI := relativeAlgebra hvw
  rw [finrank_relativeAlgebra_eq_ramification_inertia hvw]
  have he : 0 < relRamIdx v w * relInertDeg v w := by
    have h := localDeg_pos v
    rw [localDeg_eq_mul hvw] at h
    exact Nat.pos_of_mul_pos_left h
  have hw0 : (localDeg w : ℝ) ≠ 0 := by exact_mod_cast (localDeg_pos w).ne'
  have he0 : (relRamIdx v w * relInertDeg v w : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  rw [localDeg_eq_mul hvw]
  push_cast
  push_cast at he0
  field_simp [hw0, he0]

theorem inverse_relativeFinrank_mem_Ioc :
    letI := relativeAlgebra hvw
    1 / (Module.finrank (completionAt K w) (completionAt L v) : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
  letI := relativeAlgebra hvw
  have hn : 0 < Module.finrank (completionAt K w) (completionAt L v) := by
    rw [finrank_relativeAlgebra_eq_ramification_inertia hvw]
    have h := localDeg_pos v
    rw [localDeg_eq_mul hvw] at h
    exact Nat.pos_of_mul_pos_left h
  have hnR : (0 : ℝ) < Module.finrank (completionAt K w) (completionAt L v) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ Module.finrank (completionAt K w) (completionAt L v) := by exact_mod_cast hn
  exact ⟨div_pos zero_lt_one hnR, (div_le_one hnR).mpr hn1⟩

end
end JoshiTeich.Act1Scene1.LocalCompletion
