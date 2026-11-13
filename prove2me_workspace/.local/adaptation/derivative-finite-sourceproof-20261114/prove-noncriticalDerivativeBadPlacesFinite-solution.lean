import Definitions.Def_FermatNoncriticalFunctions
import Definitions.Def_FermatCurveDerivationLocalization

set_option autoImplicit false
open AbcAdaptation
open AbcAdaptation.Tripod.Fermat.Proper

/-- The actual derivative with respect to ψ preserves all but finitely many
actual local rings containing ψ, over the full valuative place carrier. -/
theorem solution {N : ℕ} (M : Model N)
    (ψ : M.K) (hψ : Transcendental ℚ ψ) :
    {P : Place M.K | ψ ∈ P.1 ∧
      ∃ s ∈ P.1, CurveDeriv.derivAlong ψ s ∉ P.1}.Finite := by
  letI : IsCurveField M.K := M.isCurveField
  haveI : Fact (Transcendental ℚ ψ) := ⟨hψ⟩
  letI : Algebra (Algebra.adjoin ℚ {ψ}) (chartRing ψ) := (chartRing ψ).algebra'
  letI : Module (Algebra.adjoin ℚ {ψ}) (chartRing ψ) := Algebra.toModule
  obtain ⟨G, hG⟩ := Module.Finite.fg_top
    (R := Algebra.adjoin ℚ {ψ}) (M := chartRing ψ)
  refine (G.finite_toSet.biUnion fun g _ ↦
    Place.finite_setOf_notMem (CurveDeriv.derivAlong ψ (g : M.K))).subset ?_
  rintro P ⟨hψP, s, hs, hDs⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  by_contra hgood
  push Not at hgood
  apply hDs
  have hA : ∀ r : chartRing ψ, CurveDeriv.derivAlong ψ (r : M.K) ∈ P.1 :=
    CurveDeriv.derivAlong_mem_chartRing_of_generators hψ P hψP G hG hgood
  exact CurveDeriv.derivAlong_mem_place_of_chartRing P hψP hA hs
