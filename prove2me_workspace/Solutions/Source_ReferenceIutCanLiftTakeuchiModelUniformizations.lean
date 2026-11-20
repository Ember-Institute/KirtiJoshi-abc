/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/S1/Main.lean, lines 82–108
-/
import Solutions.Source_ReferenceIutCanLiftTakeuchiBelyi
import Solutions.Source_ReferenceIutCanLiftTakeuchiCertificates
import Solutions.Source_ReferenceIutCanLiftTakeuchiTransport

set_option autoImplicit false

open scoped MatrixGroups

namespace AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi

/-- Each of the four model curves is uniformized by a Takeuchi group. -/
theorem exists_uniformizes_ccurve (k : Fin 4) :
    ∃ A B : SL(2, ℝ), Uniformizes (ccurve k) (A, B) ∧ IsTakeuchiConj A B := by
  obtain ⟨f, N, D, H, K, R, c, hc, h1, h3, hf⟩ := exists_modelRatCert k
  exact exists_takeuchi jOrbStatement hc (ccurve k) h1 h3 hf

/-- Each model curve has a uniformization by one of the four explicit pairs. -/
theorem exists_takeuchiPair_ccurve (k : Fin 4) :
    ∃ i, Uniformizes (ccurve k) (takeuchiPair i) ∨
      Uniformizes ((ccurve k).map (starRingEnd ℂ)) (takeuchiPair i) := by
  obtain ⟨A, B, hU, A', B', hcl, i, A'', hA'', B'', hB'', g, hgA, hgB⟩ :=
    exists_uniformizes_ccurve k
  exact ⟨i, uniformizes_takeuchiPair_of_conjugacy (ccurve k) A B A' B' hU hcl
    i A'' B'' hA'' hB'' g hgA hgB⟩

end AbcAdaptation.Reference.Iut.Anabelian.CanLiftAnalytic.Takeuchi
