import Mathlib.Analysis.Normed.Field.Dense

/-!
source-id: JT-SCENE1-COMPLETE-FIELD-APPROXIMATE-ROOTS
source: completeness of normed fields and finite splitting-field root sets;
Mathlib spectral norm, closed isometric embeddings and polynomial splitting.
fidelity: a monic polynomial over a complete ultrametric field has a root
if its evaluation norm can be arbitrarily small. The proof uses the original
field's closed image in a finite splitting field. No algebraic closedness,
root convergence or root certificate is assumed. Original proofs; R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.CompleteFieldApproximateRoots

open Polynomial
open scoped Topology
universe u v
noncomputable section

/-- Finitely many points outside a closed field image have a common positive separation. -/
theorem finite_separation {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
    {L : Type v} [NormedField L] [NormedAlgebra K L] (s : Multiset L)
    (hno : ∀ a ∈ s, a ∉ Set.range (algebraMap K L)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ s, ∀ x : K, δ ≤ ‖algebraMap K L x - a‖ := by
  have hi : Isometry (algebraMap K L) := by
    apply isometry_iff_dist_eq.mpr
    intro x y
    rw [dist_eq_norm, ← map_sub, norm_algebraMap', dist_eq_norm]
  have hc := hi.isClosedEmbedding.isClosed_range
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | cons a s ih =>
    obtain ⟨δ, hδ, hb⟩ := ih (fun r hr => hno r (Multiset.mem_cons_of_mem hr))
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hc.isOpen_compl a (hno a (Multiset.mem_cons_self _ _))
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro r hr x
    rcases Multiset.mem_cons.mp hr with rfl | hr
    · apply (min_le_right δ ε).trans
      apply le_of_not_gt
      intro hx
      have hm : algebraMap K L x ∈ Metric.ball r ε := by
        rwa [Metric.mem_ball, dist_eq_norm]
      exact hball hm ⟨x, rfl⟩
    · exact (min_le_left δ ε).trans (hb r hr x)

/-- Arbitrarily small evaluation norms force a root in the same complete field. -/
theorem exists_root {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (P : Polynomial K) (hP : P.Monic)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ x : K, ‖P.eval x‖ < ε) : ∃ x : K, P.eval x = 0 := by
  by_contra hroot
  push Not at hroot
  let L := P.SplittingField
  let : NormedField L := spectralNorm.normedField K L
  let : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  let Q := P.map (algebraMap K L)
  have hQ : Q.Monic := hP.map _
  have hs : Q.Splits := SplittingField.splits P
  have hno : ∀ a ∈ Q.roots, a ∉ Set.range (algebraMap K L) := by
    intro a ha ⟨x, hx⟩
    have he : Q.eval a = 0 := (Polynomial.mem_roots hQ.ne_zero).mp ha
    rw [← hx, Polynomial.eval_map_apply] at he
    exact hroot x ((algebraMap K L).injective (he.trans (map_zero _).symm))
  obtain ⟨δ, hδ, hsep⟩ := finite_separation Q.roots hno
  obtain ⟨x, hx⟩ := happrox (δ ^ Q.roots.card) (pow_pos hδ _)
  have hprod : δ ^ Q.roots.card ≤ (Q.roots.map (fun a => ‖algebraMap K L x - a‖)).prod := by
    have h := Multiset.prod_map_le_prod_map₀ (fun _ : L => δ)
      (fun a => ‖algebraMap K L x - a‖) (fun _ _ => hδ.le) (fun a ha => hsep a ha x)
    simpa only [Multiset.map_const', Multiset.prod_replicate] using h
  have heval : ‖P.eval x‖ = (Q.roots.map (fun a => ‖algebraMap K L x - a‖)).prod := by
    rw [← norm_algebraMap' L (P.eval x), ← Polynomial.eval_map_apply,
      hs.eval_eq_prod_roots_of_monic hQ]
    simpa [Multiset.map_map, Function.comp_def, normHom] using
      (map_multiset_prod (normHom.toMonoidHom : L →* ℝ)
        (Q.roots.map (fun a => algebraMap K L x - a)))
  have hbound : δ ^ Q.roots.card ≤ ‖P.eval x‖ := by rw [heval]; exact hprod
  exact (not_lt_of_ge hbound) hx

end
end JoshiTeich.Act1Scene1.CompleteFieldApproximateRoots
