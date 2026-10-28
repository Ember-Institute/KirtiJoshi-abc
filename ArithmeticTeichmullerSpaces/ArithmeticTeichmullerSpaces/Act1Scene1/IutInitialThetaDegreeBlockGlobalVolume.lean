import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDegreeBlockGroupedRegionVolume
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRelativeQRootProduct
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRelativeQRootReferenceBound

/-!
source-id: JT-SCENE1-INITIAL-THETA-DEGREE-BLOCK-GLOBAL-VOLUME
source: Joshi III `ss:weighted-vol`, `eq:weights` (3522--3557), the actual
finite residue-characteristic decomposition of the selected q-root source, and
the proved grouped degree-block root volumes.
fidelity: assembles the actual grouped root volumes over the finite rational
prime support of the selected q-root source. It proves positivity and
an exact finite sum formula for the negative logarithm by consuming the local
block identities. This remains an actual finite product and does not identify
it with a paper theta-volume or a paper carrier.
boundary: Scene1/Derived; paper `L'`, mixed-moduli descent, and producer laws
remain open. Original proofs; no reference implementation copied.
-/

namespace JoshiTeich.Act1Scene1.DegreeBlockGlobalVolume

open JoshiTeich.Prologue SelectedDegreeBlockVolume DegreeBlockGroupedRegionVolume
open scoped BigOperators Classical
universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

abbrev SelectedSource :=
  {s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset //
    s ∈ iutInitialThetaOddSupportSelectedQRootSourcePlaces D}

noncomputable instance selectedSourceFintype : Fintype (SelectedSource D) :=
  (iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite D).fintype

noncomputable def selectedPrimeSupportFinset : Finset ℕ :=
  (Finset.univ : Finset (SelectedSource D)).image
    (fun s => Arithmetic.residueChar s.1.1)

abbrev PrimeSupport := {p : ℕ // p ∈ selectedPrimeSupportFinset D}

theorem primeProof (p : PrimeSupport D) : p.1.Prime := by
  obtain ⟨s, hs, hsp⟩ := Finset.mem_image.mp p.2
  have hplace : Arithmetic.residueChar s.1.1 = p.1 := hsp
  rw [← hplace]
  exact Arithmetic.residueChar_prime s.1.1

noncomputable def groupedRootVolumeAtPrime (p : PrimeSupport D) : ℝ := by
  let _ : Fact p.1.Prime := ⟨primeProof D p⟩
  exact groupedRegionVolume D p.1 (logRegions D p.1)

def groupedRootVolumeProduct : ℝ :=
  ∏ p : PrimeSupport D, groupedRootVolumeAtPrime D p

theorem groupedRootVolumeAtPrime_eq_relativeRootVolume
    (p : PrimeSupport D) :
    groupedRootVolumeAtPrime D p =
      SelectedThetaTensor.relativeRootVolume D p.1 := by
  let _ : Fact p.1.Prime := ⟨primeProof D p⟩
  exact groupedRegionVolume_logRegions_eq_relativeRootVolume D p.1

theorem groupedRootVolumeProduct_eq_relativeRootVolume_product :
    groupedRootVolumeProduct D =
      ∏ p : PrimeSupport D,
        SelectedThetaTensor.relativeRootVolume D p.1 := by
  unfold groupedRootVolumeProduct
  apply Finset.prod_congr rfl
  intro p hp
  exact groupedRootVolumeAtPrime_eq_relativeRootVolume D p

theorem groupedRootVolumeAtPrime_pos (p : PrimeSupport D) :
    0 < groupedRootVolumeAtPrime D p := by
  let _ : Fact p.1.Prime := ⟨primeProof D p⟩
  exact groupedRegionVolume_logRegions_pos D p.1

theorem groupedRootVolumeProduct_pos : 0 < groupedRootVolumeProduct D := by
  unfold groupedRootVolumeProduct
  exact Finset.prod_pos (fun p _ => groupedRootVolumeAtPrime_pos D p)

theorem groupedRootVolumeAtPrime_negLog_eq_ordp_sum
    (p : PrimeSupport D) :
    -Real.log (groupedRootVolumeAtPrime D p) =
      ∑ i : Index D p.1,
        (Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p.1 i) : ℝ) *
          Arithmetic.ordp (SelectedThetaTensor.sourceAt D p.1 i).1
            ((iutInitialThetaOddSupportTorsionQRootSource D).qroot
              (SelectedThetaTensor.sourceAt D p.1 i)) * Real.log p.1 := by
  let _ : Fact p.1.Prime := ⟨primeProof D p⟩
  exact groupedRegionVolume_logRegions_negLog_eq_ordp_sum D p.1

theorem groupedRootVolumeProduct_negLog_eq_prime_sum :
    -Real.log (groupedRootVolumeProduct D) =
      ∑ p : PrimeSupport D,
        ∑ i : Index D p.1,
          (Arithmetic.localDeg (SelectedThetaTensor.moduliAt D p.1 i) : ℝ) *
            Arithmetic.ordp (SelectedThetaTensor.sourceAt D p.1 i).1
              ((iutInitialThetaOddSupportTorsionQRootSource D).qroot
                (SelectedThetaTensor.sourceAt D p.1 i)) * Real.log p.1 := by
  rw [groupedRootVolumeProduct,
    Real.log_prod (fun p _ => (groupedRootVolumeAtPrime_pos D p).ne'),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  exact groupedRootVolumeAtPrime_negLog_eq_ordp_sum D p

def selectedSourceFromSigma
    (pi : Σ p : PrimeSupport D, Index D p.1) : SelectedSource D :=
  ⟨SelectedThetaTensor.sourceAt D pi.1.1 pi.2,
    (SelectedThetaTensor.sourceAt_selected_residueChar D pi.1.1 pi.2).1⟩

noncomputable def selectedSourceSigmaEquiv :
    (Σ p : PrimeSupport D, Index D p.1) ≃ SelectedSource D := by
  classical
  refine Equiv.ofBijective
    (selectedSourceFromSigma D) ?_
  constructor
  · rintro ⟨p, i⟩ ⟨q, j⟩ h
    have hsource :
        SelectedThetaTensor.sourceAt D p.1 i =
          SelectedThetaTensor.sourceAt D q.1 j :=
      congrArg (fun s : SelectedSource D => s.1) h
    have hpq : p.1 = q.1 := by
      have hi := (SelectedThetaTensor.sourceAt_selected_residueChar D p.1 i).2
      have hj := (SelectedThetaTensor.sourceAt_selected_residueChar D q.1 j).2
      calc
        p.1 = Arithmetic.residueChar
            (SelectedThetaTensor.sourceAt D p.1 i).1 := hi.symm
        _ = Arithmetic.residueChar
            (SelectedThetaTensor.sourceAt D q.1 j).1 :=
          by rw [hsource]
        _ = q.1 := hj
    cases Subtype.ext hpq
    have hij : i = j := by
      apply (SelectedThetaTensor.enumeration D p.1).injective
      apply Subtype.ext
      exact hsource
    exact Sigma.ext rfl (heq_of_eq hij)
  · intro s
    have hsPrime : Arithmetic.residueChar s.1.1 ∈
        selectedPrimeSupportFinset D :=
      Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
    have hsFiber : s.1 ∈ SelectedThetaTensor.fiber D (Arithmetic.residueChar s.1.1) := by
      rw [SelectedThetaTensor.fiber, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, s.2, rfl⟩
    let p : PrimeSupport D := ⟨Arithmetic.residueChar s.1.1, hsPrime⟩
    let sf : ↥(SelectedThetaTensor.fiber D p.1) := ⟨s.1, hsFiber⟩
    let i : Index D p.1 :=
      (SelectedThetaTensor.enumeration D p.1).symm sf
    refine ⟨⟨p, i⟩, ?_⟩
    apply Subtype.ext
    change (SelectedThetaTensor.enumeration D p.1 i).1 = s.1
    dsimp [i]
    rw [Equiv.apply_symm_apply]

def selectedSourceRelativeVolume : ℝ :=
  ∏ s : SelectedSource D,
    ‖(iutInitialThetaOddSupportTorsionQRootSource D).qroot s.1‖ ^
      ((Arithmetic.localDeg (iutPlaceUnder
        (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
        (Kt := ↥D.prime.torsionField) s.1.1) : ℝ) /
        Arithmetic.localDeg s.1.1)

theorem groupedRootVolumeProduct_eq_selectedSourceRelativeVolume :
    groupedRootVolumeProduct D = selectedSourceRelativeVolume D := by
  rw [groupedRootVolumeProduct_eq_relativeRootVolume_product D]
  unfold SelectedThetaTensor.relativeRootVolume selectedSourceRelativeVolume
  rw [← Fintype.prod_sigma']
  apply Fintype.prod_equiv (selectedSourceSigmaEquiv D) _ _
  intro pi
  let _ : Fact pi.1.1.Prime := ⟨primeProof D pi.1⟩
  have hsource : (selectedSourceSigmaEquiv D pi).1 =
      SelectedThetaTensor.sourceAt D pi.1.1 pi.2 := by
    rfl
  rw [hsource, SelectedThetaTensor.relativeWeight_eq_localDeg_ratio D pi.1.1 pi.2]

theorem selectedSourceRelativeVolume_eq_relativeQRootProduct :
    selectedSourceRelativeVolume D =
      iutInitialThetaRelativeQRootProduct D := by
  unfold selectedSourceRelativeVolume iutInitialThetaRelativeQRootProduct
  let e := iutInitialThetaModuliSelectedSourceEquiv D
  symm
  apply Fintype.prod_equiv e
  intro v
  rw [iutInitialThetaRelativeQRootFactor_eq_localDeg_ratio D v]
  have hunder :
      iutPlaceUnder
          (F := ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E))
          (Kt := ↥D.prime.torsionField)
          ((iutInitialThetaModuliSelectedSourceEquiv D v).1.1) = v.1 :=
    (iutPlaceUnder_eq_of_liesOver (iutInitialThetaModuliSelectedSource_liesOver D v)).symm
  simp only [e]
  rw [hunder]

theorem groupedRootVolumeProduct_eq_relativeQRootProduct :
    groupedRootVolumeProduct D = iutInitialThetaRelativeQRootProduct D := by
  rw [groupedRootVolumeProduct_eq_selectedSourceRelativeVolume D,
    selectedSourceRelativeVolume_eq_relativeQRootProduct D]

theorem groupedRootVolumeProduct_normalized_eq_normalizedRelativeQRootProduct :
    groupedRootVolumeProduct D ^
        (1 / (Module.finrank ℚ
          ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ)) =
      iutInitialThetaNormalizedRelativeQRootProduct D := by
  rw [groupedRootVolumeProduct_eq_relativeQRootProduct D]
  rfl

theorem groupedRootVolumeProduct_normalized_negLog_eq_fullBaseSum :
    -Real.log (groupedRootVolumeProduct D ^
        (1 / (Module.finrank ℚ
          ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))) =
      iutInitialThetaFullBaseQPilotLogSum D := by
  rw [groupedRootVolumeProduct_normalized_eq_normalizedRelativeQRootProduct D]
  exact iutInitialThetaNormalizedRelativeQRootProduct_negLog_eq_fullBaseSum D

theorem groupedRootVolumeProduct_normalized_negLog_ge_referenceAbsLogQ :
    JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) ≤
      -Real.log (groupedRootVolumeProduct D ^
        (1 / (Module.finrank ℚ
          ↥(JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E) : ℝ))) := by
  rw [groupedRootVolumeProduct_normalized_eq_normalizedRelativeQRootProduct D]
  exact iutInitialThetaReferenceAbsLogQ_le_normalizedRelativeQRootProduct_negLog D

theorem groupedRootVolumeProduct_lt_one_of_selectedSource
    (hs : Nonempty (SelectedSource D)) :
    groupedRootVolumeProduct D < 1 := by
  have hfactor (p : PrimeSupport D) :
      0 < groupedRootVolumeAtPrime D p ∧ groupedRootVolumeAtPrime D p < 1 := by
    obtain ⟨s, hsUniv, hsp⟩ := Finset.mem_image.mp p.2
    have hindex : Nonempty (Index D p.1) :=
      (selectedIndex_nonempty_iff_sourceAtPrime D p.1).mpr
        ⟨s.1, s.2, hsp⟩
    let _ : Fact p.1.Prime := ⟨primeProof D p⟩
    exact ⟨groupedRegionVolume_logRegions_pos D p.1,
      groupedRegionVolume_logRegions_lt_one D p.1 hindex⟩
  have hprime : Nonempty (PrimeSupport D) := by
    obtain ⟨s⟩ := hs
    refine ⟨⟨Arithmetic.residueChar s.1.1,
      Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩⟩⟩
  have hprod : ∀ t : Finset (PrimeSupport D), t.Nonempty →
      (∀ p ∈ t, 0 < groupedRootVolumeAtPrime D p) →
      (∀ p ∈ t, groupedRootVolumeAtPrime D p < 1) →
      t.prod (groupedRootVolumeAtPrime D) < 1 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro ht
      simp at ht
    | @insert a t ha ih =>
      intro ht hpos hlt
      by_cases ht' : t.Nonempty
      · have hrest := ih ht'
          (fun p hp => hpos p (Finset.mem_insert_of_mem hp))
          (fun p hp => hlt p (Finset.mem_insert_of_mem hp))
        rw [Finset.prod_insert ha]
        exact (mul_lt_of_lt_one_right (hpos a (Finset.mem_insert_self _ _)) hrest).trans
          (hlt a (Finset.mem_insert_self _ _))
      · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht'
        subst t
        simpa using hlt a (Finset.mem_insert_self _ _)
  exact hprod Finset.univ ⟨Classical.choice hprime, Finset.mem_univ _⟩
    (fun p hp => (hfactor p).1) (fun p hp => (hfactor p).2)

theorem groupedRootVolumeProduct_eq_one_iff_no_selectedSource :
    groupedRootVolumeProduct D = 1 ↔ ¬ Nonempty (SelectedSource D) := by
  constructor
  · intro hvol
    by_contra hs
    exact (ne_of_lt (groupedRootVolumeProduct_lt_one_of_selectedSource D hs)) hvol
  · intro hs
    let _ : IsEmpty (SelectedSource D) := ⟨fun s => hs ⟨s⟩⟩
    let _ : IsEmpty (PrimeSupport D) := ⟨fun p => by
      obtain ⟨s, hsUniv, hsp⟩ := Finset.mem_image.mp p.2
      exact hs ⟨s⟩⟩
    simp [groupedRootVolumeProduct]

end
end JoshiTeich.Act1Scene1.DegreeBlockGlobalVolume
