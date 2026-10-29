import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQNormalizationBridge

/-!
source-id: JT-SCENE1-INITIAL-THETA-DEGREE-PAPER-FACTOR-BRIDGE
source: the raw q-factor, global degree-normalized q-factor, and local
residue-degree-normalized paper q-factor definitions.
fidelity: proves the exact power conversion between the two normalized
presentations on the same actual source index. No paper carrier, weight law,
or theta-volume identity is inferred.
boundary: Scene1/Derived. Original proof; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
universe u
noncomputable section

theorem degreeNormalizedSourceQFactor_eq_paperNormalizedSourceQFactor_rpow
    {K : Type u} [Field K] [NumberField K]
    {O : Type u} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data K O p)
    (i : Corollary312SourceQIndex p T) :
    Corollary312DegreeNormalizedSourceQFactor p T i =
      Corollary312PaperNormalizedSourceQFactor p T i ^
        ((Arithmetic.inertDeg i.1 : ℝ) /
          (Module.finrank ℚ K : ℝ)) := by
  have hRaw : 0 < Corollary312SourceQFactor p T i := by
    unfold Corollary312SourceQFactor
    exact Real.rpow_pos_of_pos
      (T.scene1.input_laws.first_axiom.q_norm_positive i.1 i.2) _
  have hInert : (Arithmetic.inertDeg i.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Arithmetic.inertDeg_pos i.1).ne'
  have hGlobal : (Module.finrank ℚ K : ℝ) ≠ 0 :=
    (show (0 : ℝ) < Module.finrank ℚ K from Arithmetic.finrank_pos).ne'
  unfold Corollary312DegreeNormalizedSourceQFactor
    Corollary312PaperNormalizedSourceQFactor
  calc
    Corollary312SourceQFactor p T i ^ (1 / (Module.finrank ℚ K : ℝ)) =
        Corollary312SourceQFactor p T i ^
          ((1 / (Arithmetic.inertDeg i.1 : ℝ)) *
            ((Arithmetic.inertDeg i.1 : ℝ) / (Module.finrank ℚ K : ℝ))) := by
      congr 1
      field_simp [hInert, hGlobal]
    _ = (Corollary312SourceQFactor p T i ^
          (1 / (Arithmetic.inertDeg i.1 : ℝ))) ^
          ((Arithmetic.inertDeg i.1 : ℝ) / (Module.finrank ℚ K : ℝ)) := by
      rw [Real.rpow_mul hRaw.le]

end
end JoshiTeich.Act1Scene1
