/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors
-/
import Definitions.Def_FermatLocalBelyi

set_option autoImplicit false

open Filter

namespace AbcAdaptation.Tripod.Fermat.Proper

theorem boundedBelyiImages_of_children {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (A : AffineIdentification M)
    (hCompact : LocalCompactness M)
    (hRegular : AvoidanceRegularity M hDVR)
    (hSelect : NoncriticalSelection M hDVR)
    (hEmbedding : EmbeddingBoundsToSet M) : BoundedBelyiImages M hDVR A := by
  intro d xs hxs
  have hdeg : ∀ n, (affineLift M A (xs n)).degree ≤ d := by
    intro n
    rw [affineLift_degree_eq]
    exact hxs n
  obtain ⟨s, hs, T, hT⟩ := hCompact d (fun n => affineLift M A (xs n)) hdeg
  obtain ⟨φ, hφ, hφT⟩ := hSelect T
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    exact hφ.1 isAlgebraic_zero
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    exact hφ.1 isAlgebraic_one
  obtain ⟨c, hc⟩ := hT φ hφ0 hφ1 (fun P hP => hRegular φ P (hφT P hP))
  obtain ⟨cut, hcut⟩ := Filter.eventually_atTop.mp hc
  refine ⟨φ, hφ, (fun n => s (n + cut)), ?_, localCompactSet d c, ?_⟩
  · intro i j hij
    exact hs (Nat.add_lt_add_right hij cut)
  · intro n
    have hn : cut ≤ n + cut := by omega
    have hlocal := hcut (n + cut) hn
    have hgood : GoodValue M (affineLift M A (xs (s (n + cut)))) φ := by
      obtain ⟨hreg, h0, h1, -, -⟩ := hlocal
      exact ⟨hreg, h0, h1⟩
    exact ⟨hgood, hEmbedding _ φ d c (hdeg _) hlocal,
      (belyiImage_degree_le M A φ _ hgood).trans (hxs _)⟩

end AbcAdaptation.Tripod.Fermat.Proper
