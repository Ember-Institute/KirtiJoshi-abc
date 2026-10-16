import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionRelativeDegree
import ArithmeticTeichmullerSpaces.Act1Scene1.IutPlacesOver

/-!
source-id: JT-SCENE1-COMPLETION-DEGREE-ONE
source: actual local degree sum, relative completion degree and algebraMap.
fidelity: a degree-one extension of number fields induces a surjective
completion map at every pair of places lying over each other.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion
open NumberField JoshiTeich.Prologue.Arithmetic
open scoped Classical BigOperators
universe u
noncomputable section
variable {F K : Type u} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
variable {w : FinitePlace F} {v : FinitePlace K}

theorem relativeDegree_eq_one_of_finrank_eq_one
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (hdeg : Module.finrank F K = 1) : relRamIdx v w * relInertDeg v w = 1 := by
  let hs := finite_places_liesOver (K := K) w
  have hsum := sum_localDeg_liesOver w hs.toFinset (fun z => hs.mem_toFinset)
  have hv : v ∈ hs.toFinset := hs.mem_toFinset.mpr hvw
  have hle : localDeg v ≤ localDeg w := by
    have h := Finset.single_le_sum (fun z _ => Nat.zero_le (localDeg z)) hv
    rw [hsum, hdeg, one_mul] at h
    exact h
  have he := localDeg_eq_mul hvw
  have hp := localDeg_pos v
  have hw := localDeg_pos w
  nlinarith

theorem embedCompletion_surjective_of_finrank_eq_one
    (hvw : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
    (hdeg : Module.finrank F K = 1) : Function.Surjective (iutEmbedCompletion hvw) := by
  letI := relativeAlgebra hvw
  have hlocal : Module.finrank (completionAt F w) (completionAt K v) = 1 := by
    rw [finrank_relativeAlgebra_eq_ramification_inertia hvw]
    exact relativeDegree_eq_one_of_finrank_eq_one hvw hdeg
  exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hlocal).2

end
end JoshiTeich.Act1Scene1.LocalCompletion
