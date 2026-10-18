import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaArchimedeanPacketRegion

/-!
source-id: JT-SCENE1-INITIAL-THETA-ARCHIMEDEAN-PACKET-LOG-VOLUME
source: reference Concrete/Container, weight / tupleWeight / vol, and
Cor312/LogVolume, packetVol_product; Joshi III ss:weighted-vol.
fidelity: actual infinite-place factors have real dimension mult(v).
Cancels tensor dimension against actual tuple weights on arbitrary positive
finite component regions, then consumes the identity on the existing source.
Original proofs; no reference source code copied.
boundary: Scene1/Derived; no paper representative or thetaVolume identity.
-/

namespace JoshiTeich.Act1Scene1.LocalArchimedean

open NumberField
open scoped BigOperators Classical
universe u
noncomputable section
variable {K : Type u} [Field K]

theorem factor_finrank_eq_mult (v : InfinitePlace K) :
    Module.finrank ℝ (Factor v) = v.mult := by
  change Module.finrank ℝ (ULift.{u} (archField v)) = v.mult
  rw [finrank_ulift]
  by_cases hv : v.IsReal
  · rw [archField_of_isReal hv, Subalgebra.finrank_bot, hv.mult_eq_one]
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hv
    rw [archField_of_isComplex hc, hc.mult_eq_two]
    exact (Subalgebra.topEquiv.toLinearEquiv.finrank_eq).trans Complex.finrank_real_complex

theorem tensor_finrank_eq_mult_prod {ι : Type} [Fintype ι] (c : ι → InfinitePlace K) :
    Module.finrank ℝ (Tensor c) = ∏ i, (c i).mult := by
  rw [Module.finrank_eq_card_basis (tensorBasis c)]
  simp only [BasisIndex, Fintype.card_pi, Fintype.card_fin, factor_finrank_eq_mult]

end
end JoshiTeich.Act1Scene1.LocalArchimedean

namespace JoshiTeich.Act1Scene1.IutInitialThetaArchimedeanPacketLogVolume

open NumberField MeasureTheory IutInitialThetaArchimedeanPacketRegion
open scoped BigOperators Classical
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem tupleWeight_eq_dimension_div_degree (j : ℕ) (c : Tuple D j) :
    tupleWeight D j c = (Module.finrank ℝ (LocalArchimedean.Tensor c) : ℝ) /
      (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
  rw [LocalArchimedean.tensor_finrank_eq_mult_prod]
  simp only [tupleWeight, placeWeight, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Nat.cast_prod]

theorem weighted_normalizationLogVolume (j : ℕ) (c : Tuple D j)
    (U : Set (LocalArchimedean.Tensor c)) :
    tupleWeight D j c * LocalArchimedean.normalizationLogVolume c U =
      Real.log (LocalArchimedean.normalizedHaar c U).toReal /
        (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
  have hd : (Module.finrank ℝ (LocalArchimedean.Tensor c) : ℝ) ≠ 0 := by
    exact_mod_cast (LocalArchimedean.tensor_finrank_pos c).ne'
  rw [tupleWeight_eq_dimension_div_degree, LocalArchimedean.normalizationLogVolume]
  field_simp

def familyLogVolume (j : ℕ) (U : ∀ c : Tuple D j, Set (LocalArchimedean.Tensor c)) : ℝ :=
  ∑ c, tupleWeight D j c * LocalArchimedean.normalizationLogVolume c (U c)

theorem familyLogVolume_eq_productMeasure_log (j : ℕ)
    (U : ∀ c : Tuple D j, Set (LocalArchimedean.Tensor c))
    (hpos : ∀ c, 0 < LocalArchimedean.normalizedHaar c (U c))
    (hfin : ∀ c, LocalArchimedean.normalizedHaar c (U c) < ⊤) :
    familyLogVolume D j U =
      Real.log (productMeasure D j (Set.pi Set.univ U)).toReal /
        (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
  have hprod : productMeasure D j (Set.pi Set.univ U) =
      ∏ c : Tuple D j, LocalArchimedean.normalizedHaar c (U c) := Measure.pi_pi _ _
  calc
    _ = (∑ c : Tuple D j, Real.log (LocalArchimedean.normalizedHaar c (U c)).toReal) /
        (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) := by
      simp only [familyLogVolume, weighted_normalizationLogVolume, Finset.sum_div]
    _ = _ := by
      rw [hprod, ENNReal.toReal_prod, Real.log_prod]
      intro c _
      exact (ENNReal.toReal_pos (hpos c).ne' (hfin c).ne).ne'

theorem packetLogVolume_eq_productMeasure_log (j : ℕ) :
    packetLogVolume D j = Real.log (productMeasure D j (region D j)).toReal /
      (Module.finrank ℚ ↥D.prime.torsionField : ℝ) ^ (j + 1) :=
  familyLogVolume_eq_productMeasure_log D j _
    (fun c => (LocalArchimedean.factorOrbit_archLogShell_haar_pos_lt_top c).1)
    (fun c => (LocalArchimedean.factorOrbit_archLogShell_haar_pos_lt_top c).2)

end
end JoshiTeich.Act1Scene1.IutInitialThetaArchimedeanPacketLogVolume
