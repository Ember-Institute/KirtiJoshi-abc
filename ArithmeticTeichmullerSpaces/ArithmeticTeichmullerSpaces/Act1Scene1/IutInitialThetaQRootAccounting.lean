import ArithmeticTeichmullerSpaces.Act1Scene1.IutTateFamilyQRootAdapter
import ArithmeticTeichmullerSpaces.Act1Scene1.IutQRootAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBadPlaceFiniteness
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.LeftHandSide

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open JoshiTeich.Prologue.Arithmetic
open WithZero
open scoped BigOperators Classical NumberField Valued

universe u

noncomputable section

set_option maxHeartbeats 1000000

/-!
source-id: IUT-COR312-INITIAL-THETA-QROOT-ACCOUNTING
source: `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean`,
`thetaLocalData` and `sum_weight_ordp_qroot`; the valuation source is
`refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`, `unif`,
`unif_isUniformizer`, `q_order_coprime`, and `qOrder`. The global q-pilot
formula is `refer/iut/Iut/Cor312/LeftHandSide.lean`, `QPilotData.absLogQ`;
the degree weight follows `refer/iut/Iut/Concrete/ThetaRegion.lean`,
`QPilotInputs.qPilot`.
fidelity: specializes the project q-root weighted-sum transfer to actual
`InitialThetaData`. It constructs the completion valuation from the real
admissible-prime fields, proves the per-rational-prime q-degree identity, and
groups those identities into the actual IUT `QPilotData.absLogQ` formula. It
does not identify the Scene1 link carrier, construct `V_p^oss`, or freeze the
target q-factor normalization.
boundary: Scene1/Derived
-/

variable {F : Type u} [Field F] [NumberField F]

namespace IutCompletionTateValuation

/-- Build the completion Tate valuation from the chosen uniformizer and normalized
order carried by the actual IUT admissible-prime source. -/
noncomputable def ofInitialThetaData
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    :
    IutCompletionTateValuation
      (IutBaseQPilotSource.ofInitialThetaData D) := by
  let B := IutBaseQPilotSource.ofInitialThetaData D
  refine IutCompletionTateValuation.ofIutNormalizedOrder
    (uniformizer := fun w => D.prime.unif w.1 (B.mem_badPlaces w))
    (hUniformizer := ?_)
    (sourceOrder := fun w => D.prime.qOrder w.1 (B.mem_badPlaces w))
    (sourceOrder_norm_eq := ?_)
    (sourceOrder_coprime := ?_)
  · intro w
    let hπ := D.prime.unif_isUniformizer w.1 (B.mem_badPlaces w)
    exact ⟨hπ.ne_zero, hπ.norm_lt_one, hπ.generates⟩
  · intro w
    let hw := B.mem_badPlaces w
    change ‖((D.prime.tate w.1 hw).q :
      w.1.maximalIdeal.adicCompletion D.F)‖ =
      ‖D.prime.unif w.1 hw‖ ^ D.prime.qOrder w.1 hw
    exact (D.prime.tate w.1 hw).norm_q_eq_pow_orderNat
      (D.prime.unif_isUniformizer w.1 hw)
  · intro w
    let hw := B.mem_badPlaces w
    have hcop : Nat.Coprime D.prime.ℓ (D.prime.qOrder w.1 hw) := by
      change Nat.Coprime D.prime.ℓ
        ((D.prime.tate w.1 hw).toOrdered
          (D.prime.unif_isUniformizer w.1 hw)).orderNat
      exact ((D.prime.tate w.1 hw).toOrdered_primeToOrder_iff
        (D.prime.unif_isUniformizer w.1 hw) D.prime.ℓ).mp
        (D.prime.q_order_coprime w.1 hw)
    exact hcop

theorem ofInitialThetaData_order_eq
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (w : (IutBaseQPilotSource.ofInitialThetaData D).badFinset) :
    (ofInitialThetaData D).orderedQOrder w =
      D.prime.qOrder w.1
        ((IutBaseQPilotSource.ofInitialThetaData D).mem_badPlaces w) := by
  let B := IutBaseQPilotSource.ofInitialThetaData D
  let hUniformizer := fun i : B.badFinset =>
    D.prime.unif i.1 (B.mem_badPlaces i)
  have hUniformizerCert : ∀ i : B.badFinset,
      Arithmetic.IsCompletionUniformizer i.1 (hUniformizer i) := by
    intro i
    dsimp [hUniformizer]
    let hπ := D.prime.unif_isUniformizer i.1 (B.mem_badPlaces i)
    exact ⟨hπ.ne_zero, hπ.norm_lt_one, hπ.generates⟩
  let hOrder := fun i : B.badFinset =>
    D.prime.qOrder i.1 (B.mem_badPlaces i)
  have hNorm := fun i : B.badFinset => by
    let hi := B.mem_badPlaces i
    change ‖((D.prime.tate i.1 hi).q :
      i.1.maximalIdeal.adicCompletion D.F)‖ =
      ‖D.prime.unif i.1 hi‖ ^ D.prime.qOrder i.1 hi
    exact (D.prime.tate i.1 hi).norm_q_eq_pow_orderNat
      (D.prime.unif_isUniformizer i.1 hi)
  have hOrderEq := IutCompletionTateValuation.ofIutNormalizedOrder_order_eq
      (B := B) hUniformizer hUniformizerCert hOrder
      (fun i => by
        change ‖((D.prime.tate i.1 (B.mem_badPlaces i)).q :
          i.1.maximalIdeal.adicCompletion D.F)‖ =
          ‖D.prime.unif i.1 (B.mem_badPlaces i)‖ ^
            D.prime.qOrder i.1 (B.mem_badPlaces i)
        exact hNorm i)
      (fun i => by
        let hi := B.mem_badPlaces i
        have hcop : Nat.Coprime D.prime.ℓ (D.prime.qOrder i.1 hi) := by
          change Nat.Coprime D.prime.ℓ
            ((D.prime.tate i.1 hi).toOrdered
              (D.prime.unif_isUniformizer i.1 hi)).orderNat
          exact ((D.prime.tate i.1 hi).toOrdered_primeToOrder_iff
            (D.prime.unif_isUniformizer i.1 hi) D.prime.ℓ).mp
            (D.prime.q_order_coprime i.1 hi)
        simpa [hOrder] using hcop) w
  simpa [IutCompletionTateValuation.ofInitialThetaData, B] using hOrderEq

end IutCompletionTateValuation

namespace IutTorsionQRootSource

/-- The concrete IUT q-pilot data for actual `InitialThetaData`, with the
degree weight used by `JoshiTeich.ReferenceIut.Concrete.ThetaRegion.QPilotInputs.qPilot`. -/
noncomputable def iutInitialThetaQPilotData
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) : JoshiTeich.ReferenceIut.QPilotData D := by
  let B := IutBaseQPilotSource.ofInitialThetaData D
  exact
    { badFinset := B.badFinset
      badFinset_spec := B.badFinset_spec
      weight := Arithmetic.qPilotWeight
      weight_pos := fun w _ => Arithmetic.qPilotWeight_pos w }

/-- Build the torsion q-root source from actual `InitialThetaData`; its base
bad-place finiteness is derived from the curve's multiplicative support. -/
noncomputable def ofInitialThetaDataFromGlobal
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    IutTorsionQRootSource D.F ↥D.prime.torsionField D.prime.ℓ
      (IutBaseQPilotSource.ofInitialThetaData D) := by
  exact ofInitialThetaDataOfQPilotBadPlaceFiniteness D
    (iutInitialThetaBadPlacesOver_finite D)

theorem canonical_qroot_weighted_sum_of_initialThetaData
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (p : ℕ)
    [Fintype {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p}]
    (bad : Finset (NumberField.FinitePlace D.F))
    (hbad : (↑bad : Set (NumberField.FinitePlace D.F)) =
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    ∑ v : {v : NumberField.FinitePlace ↥D.prime.torsionField //
        Arithmetic.residueChar v = p},
        Arithmetic.placeWeight v.1 *
          (if hv : v.1 ∈ iutBadPlacesOverFinset (k := D.F)
              (K := ↥D.prime.torsionField)
              (IutBaseQPilotSource.ofInitialThetaData D).badPlaces
              (IutBaseQPilotSource.ofInitialThetaData D).badPlaces_finite then
        Arithmetic.ordp v.1
              ((ofInitialThetaDataFromGlobal D).qroot ⟨v.1, hv⟩)
          else 0) =
      ∑ w ∈ bad.filter (fun w => Arithmetic.residueChar w = p),
        (Arithmetic.inertDeg w : ℝ) / Module.finrank ℚ D.F *
          (if hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad then
            (D.prime.qOrder w hw : ℝ) / (2 * (D.prime.ℓ : ℝ))
          else 0) := by
  classical
  let B := IutBaseQPilotSource.ofInitialThetaData D
  let R := IutTorsionQRootSource.ofInitialThetaDataFromGlobal D
  let C := IutCompletionTateValuation.ofInitialThetaData D
  let c : NumberField.FinitePlace D.F → ℝ := fun w =>
    if hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad then
      (D.prime.qOrder w hw : ℝ) / (2 * (D.prime.ℓ : ℝ))
    else 0
  have hc : ∀ w : B.badFinset,
      c w.1 = (B.qOrder w : ℝ) / (2 * (D.prime.ℓ : ℝ)) := by
    intro w
    have hqOrder : B.qOrder w = D.prime.qOrder w.1 (B.mem_badPlaces w) := by
      calc
        B.qOrder w = C.orderedQOrder w := C.completionQOrder_eq_orderNat w
        _ = D.prime.qOrder w.1 (B.mem_badPlaces w) :=
          IutCompletionTateValuation.ofInitialThetaData_order_eq D w
    have hplaces : w.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
      B.mem_badPlaces w
    simp only [c, dite_eq_left hplaces]
    rw [hqOrder]
  have hbadB : (↑bad : Set (NumberField.FinitePlace D.F)) = B.badPlaces := by
    change (↑bad : Set (NumberField.FinitePlace D.F)) =
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad
    exact hbad
  have hsum := IutTorsionQRootSource.canonical_qroot_weighted_sum_of_tateValuation
    (B := B) p bad hbadB c hc R.qroot R.qroot_pow_eq C
    D.prime.ℓ_prime.pos
  calc
    _ = ∑ w ∈ bad.filter (fun w => Arithmetic.residueChar w = p),
        (Arithmetic.inertDeg w : ℝ) / Module.finrank ℚ D.F * c w := hsum
    _ = ∑ w ∈ bad.filter (fun w => Arithmetic.residueChar w = p),
        (Arithmetic.inertDeg w : ℝ) / Module.finrank ℚ D.F *
          (if hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad then
            (D.prime.qOrder w hw : ℝ) / (2 * (D.prime.ℓ : ℝ))
          else 0) := by
      simp [c]

/-- The actual q-root weighted sum over the torsion-field places of residue
characteristic `p`, with finiteness supplied by `Arithmetic.fiber_finite`. -/
noncomputable def canonical_qroot_weighted_fiber_of_initialThetaData
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) (p : ℕ) : ℝ := by
  letI : Finite {v : NumberField.FinitePlace ↥D.prime.torsionField //
    Arithmetic.residueChar v = p} := Arithmetic.fiber_finite p
  letI : Fintype {v : NumberField.FinitePlace ↥D.prime.torsionField //
    Arithmetic.residueChar v = p} := Fintype.ofFinite _
  let B := IutBaseQPilotSource.ofInitialThetaData D
  exact ∑ v : {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p},
    Arithmetic.placeWeight v.1 *
      (if hv : v.1 ∈ iutBadPlacesOverFinset (k := D.F)
          (K := ↥D.prime.torsionField) B.badPlaces B.badPlaces_finite then
        Arithmetic.ordp v.1
          ((ofInitialThetaDataFromGlobal D).qroot ⟨v.1, hv⟩)
      else 0)

/-- Summing the real `InitialThetaData` q-root fibers by residue characteristic
recovers the `absLogQ` of its IUT q-pilot data. -/
theorem canonical_qroot_log_sum_eq_iut_absLogQ
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}} {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG) :
    ∑ p ∈ (iutInitialThetaQPilotData D).badFinset.image
        Arithmetic.residueChar,
      Real.log p * canonical_qroot_weighted_fiber_of_initialThetaData D p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ (iutInitialThetaQPilotData D) := by
  classical
  let B := IutBaseQPilotSource.ofInitialThetaData D
  let Q := iutInitialThetaQPilotData D
  let pset := Q.badFinset.image Arithmetic.residueChar
  have hbadFinset : B.badFinset = Q.badFinset := by rfl
  let c : NumberField.FinitePlace D.F → ℝ := fun w =>
    if hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad then
      (D.prime.qOrder w hw : ℝ) / (2 * (D.prime.ℓ : ℝ))
    else 0
  have hprime (p : ℕ) :
      canonical_qroot_weighted_fiber_of_initialThetaData D p =
        ∑ w ∈ Q.badFinset.filter (fun w => Arithmetic.residueChar w = p),
          Arithmetic.qPilotWeight w * c w := by
    unfold canonical_qroot_weighted_fiber_of_initialThetaData
    letI : Finite {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p} := Arithmetic.fiber_finite p
    letI : Fintype {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p} := Fintype.ofFinite _
    rw [← hbadFinset]
    simpa [c, Arithmetic.qPilotWeight, B] using
      canonical_qroot_weighted_sum_of_initialThetaData D p B.badFinset B.badFinset_spec
  have hattach (p : ℕ) :
      (∑ w ∈ Q.badFinset.filter (fun w => Arithmetic.residueChar w = p),
        Arithmetic.qPilotWeight w * c w) =
      ∑ w ∈ Q.badFinset.attach.filter
          (fun w => Arithmetic.residueChar w.1 = p),
        Arithmetic.qPilotWeight w.1 * c w.1 := by
    calc
      _ = ∑ w ∈ Q.badFinset,
          if Arithmetic.residueChar w = p then
            Arithmetic.qPilotWeight w * c w else 0 := by
        rw [Finset.sum_filter]
      _ = ∑ w ∈ Q.badFinset.attach,
          if Arithmetic.residueChar w.1 = p then
            Arithmetic.qPilotWeight w.1 * c w.1 else 0 := by
        rw [← Finset.sum_attach]
      _ = _ := by rw [Finset.sum_filter]
  have hcomponent (p : ℕ) :
      Real.log p *
          ∑ w ∈ Q.badFinset.filter (fun w => Arithmetic.residueChar w = p),
            Arithmetic.qPilotWeight w * c w =
        (∑ w ∈ Q.badFinset.attach.filter
            (fun w => Arithmetic.residueChar w.1 = p),
          Q.weight w.1 *
            (D.prime.qOrder w.1 (Q.mem_bad w.2) : ℝ) *
              Real.log (Arithmetic.residueChar w.1)) /
          (2 * (D.prime.ℓ : ℝ)) := by
    rw [hattach p]
    calc
      _ = ∑ w ∈ Q.badFinset.attach.filter
            (fun w => Arithmetic.residueChar w.1 = p),
          (Arithmetic.qPilotWeight w.1 * c w.1) * Real.log p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w hw
        ring
      _ = ∑ w ∈ Q.badFinset.attach.filter
            (fun w => Arithmetic.residueChar w.1 = p),
          (Q.weight w.1 *
            (D.prime.qOrder w.1 (Q.mem_bad w.2) : ℝ) *
              Real.log (Arithmetic.residueChar w.1)) /
            (2 * (D.prime.ℓ : ℝ)) := by
        apply Finset.sum_congr rfl
        intro w hw
        have hchar := (Finset.mem_filter.mp hw).2
        have hbad : w.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := Q.mem_bad w.2
        have hc : c w.1 =
            (D.prime.qOrder w.1 (Q.mem_bad w.2) : ℝ) /
              (2 * (D.prime.ℓ : ℝ)) := by
          simp [c, hbad]
        have hweight : Arithmetic.qPilotWeight w.1 = Q.weight w.1 := by
          rfl
        rw [hweight, hc, hchar]
        ring
      _ = _ := by rw [Finset.sum_div]
  have hsum :
      ∑ p ∈ pset,
        (∑ w ∈ Q.badFinset.attach.filter
            (fun w => Arithmetic.residueChar w.1 = p),
          Q.weight w.1 *
            (D.prime.qOrder w.1 (Q.mem_bad w.2) : ℝ) *
              Real.log (Arithmetic.residueChar w.1)) = Q.logQ := by
    unfold JoshiTeich.ReferenceIut.QPilotData.logQ
    exact Finset.sum_fiberwise_of_maps_to
      (fun w hw => Finset.mem_image.mpr ⟨w.1, w.2, rfl⟩) _
  calc
    ∑ p ∈ pset, Real.log p *
        canonical_qroot_weighted_fiber_of_initialThetaData D p =
        ∑ p ∈ pset,
          (∑ w ∈ Q.badFinset.attach.filter
              (fun w => Arithmetic.residueChar w.1 = p),
            Q.weight w.1 *
              (D.prime.qOrder w.1 (Q.mem_bad w.2) : ℝ) *
                Real.log (Arithmetic.residueChar w.1)) /
              (2 * (D.prime.ℓ : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hprime, hcomponent]
    _ = Q.logQ / (2 * (D.prime.ℓ : ℝ)) := by
      rw [← Finset.sum_div, hsum]
    _ = JoshiTeich.ReferenceIut.QPilotData.absLogQ Q := rfl

end IutTorsionQRootSource

end

end JoshiTeich.Act1Scene1
