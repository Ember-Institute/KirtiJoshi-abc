import ArithmeticTeichmullerSpaces.Act1Scene1.IutTateFamilyQRootAdapter
import ArithmeticTeichmullerSpaces.Act1Scene1.IutQRootAccounting

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
`unif_isUniformizer`, `q_order_coprime`, and `qOrder`.
fidelity: specializes the project q-root weighted-sum transfer to actual
`InitialThetaData`. It constructs the completion valuation from the real
admissible-prime fields and proves the per-rational-prime q-degree identity.
It does not identify the Scene1 link carrier, construct `V_p^oss`, or freeze
the target q-factor normalization.
boundary: Scene1/Derived
-/

variable {F : Type u} [Field F] [NumberField F]

namespace IutCompletionTateValuation

/-- Build the completion Tate valuation from the chosen uniformizer and normalized
order carried by the actual IUT admissible-prime source. -/
noncomputable def ofInitialThetaData
    {AG : Iut.AnabelianGeometry.{u}} {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG)
    (hBadFinite : (Iut.badPlacesOver D.F D.E D.VBad).Finite) :
    IutCompletionTateValuation
      (IutBaseQPilotSource.ofAdmissiblePrimeData D.prime.ℓ D.prime hBadFinite) := by
  let B := IutBaseQPilotSource.ofAdmissiblePrimeData D.prime.ℓ D.prime hBadFinite
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
    {AG : Iut.AnabelianGeometry.{u}} {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG)
    (hBadFinite : (Iut.badPlacesOver D.F D.E D.VBad).Finite)
    (w : (IutBaseQPilotSource.ofAdmissiblePrimeData D.prime.ℓ D.prime
      hBadFinite).badFinset) :
    (ofInitialThetaData D hBadFinite).orderedQOrder w =
      D.prime.qOrder w.1
        ((IutBaseQPilotSource.ofAdmissiblePrimeData D.prime.ℓ D.prime
          hBadFinite).mem_badPlaces w) := by
  let B := IutBaseQPilotSource.ofAdmissiblePrimeData D.prime.ℓ D.prime hBadFinite
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

theorem canonical_qroot_weighted_sum_of_initialThetaData
    {AG : Iut.AnabelianGeometry.{u}} {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG)
    (hBadFinite : (Iut.badPlacesOver D.F D.E D.VBad).Finite)
    (p : ℕ)
    [Fintype {v : NumberField.FinitePlace ↥D.prime.torsionField //
      Arithmetic.residueChar v = p}]
    (bad : Finset (NumberField.FinitePlace D.F))
    (hbad : (↑bad : Set (NumberField.FinitePlace D.F)) =
      Iut.badPlacesOver D.F D.E D.VBad) :
    ∑ v : {v : NumberField.FinitePlace ↥D.prime.torsionField //
        Arithmetic.residueChar v = p},
        Arithmetic.placeWeight v.1 *
          (if hv : v.1 ∈ iutBadPlacesOverFinset (k := D.F)
              (K := ↥D.prime.torsionField)
              (IutBaseQPilotSource.ofAdmissiblePrimeData D.prime.ℓ D.prime
                hBadFinite).badPlaces
              (IutBaseQPilotSource.ofAdmissiblePrimeData D.prime.ℓ D.prime
                hBadFinite).badPlaces_finite then
        Arithmetic.ordp v.1
              ((ofInitialThetaDataOfQPilotBadPlaceFiniteness D hBadFinite).qroot
                ⟨v.1, hv⟩)
          else 0) =
      ∑ w ∈ bad.filter (fun w => Arithmetic.residueChar w = p),
        (Arithmetic.inertDeg w : ℝ) / Module.finrank ℚ D.F *
          (if hw : w ∈ Iut.badPlacesOver D.F D.E D.VBad then
            (D.prime.qOrder w hw : ℝ) / (2 * (D.prime.ℓ : ℝ))
          else 0) := by
  classical
  let B := IutBaseQPilotSource.ofAdmissiblePrimeData D.prime.ℓ D.prime hBadFinite
  let R := IutTorsionQRootSource.ofInitialThetaDataOfQPilotBadPlaceFiniteness
    D hBadFinite
  let C := IutCompletionTateValuation.ofInitialThetaData D hBadFinite
  let c : NumberField.FinitePlace D.F → ℝ := fun w =>
    if hw : w ∈ Iut.badPlacesOver D.F D.E D.VBad then
      (D.prime.qOrder w hw : ℝ) / (2 * (D.prime.ℓ : ℝ))
    else 0
  have hc : ∀ w : B.badFinset,
      c w.1 = (B.qOrder w : ℝ) / (2 * (D.prime.ℓ : ℝ)) := by
    intro w
    have hqOrder : B.qOrder w = D.prime.qOrder w.1 (B.mem_badPlaces w) := by
      calc
        B.qOrder w = C.orderedQOrder w := C.completionQOrder_eq_orderNat w
        _ = D.prime.qOrder w.1 (B.mem_badPlaces w) :=
          IutCompletionTateValuation.ofInitialThetaData_order_eq D hBadFinite w
    have hplaces : w.1 ∈ Iut.badPlacesOver D.F D.E D.VBad :=
      B.mem_badPlaces w
    simp only [c, dite_eq_left hplaces]
    rw [hqOrder]
  have hbadB : (↑bad : Set (NumberField.FinitePlace D.F)) = B.badPlaces := by
    change (↑bad : Set (NumberField.FinitePlace D.F)) =
      Iut.badPlacesOver D.F D.E D.VBad
    exact hbad
  have hsum := IutTorsionQRootSource.canonical_qroot_weighted_sum_of_tateValuation
    (B := B) p bad hbadB c hc R.qroot R.qroot_pow_eq C
    D.prime.ℓ_prime.pos
  calc
    _ = ∑ w ∈ bad.filter (fun w => Arithmetic.residueChar w = p),
        (Arithmetic.inertDeg w : ℝ) / Module.finrank ℚ D.F * c w := hsum
    _ = ∑ w ∈ bad.filter (fun w => Arithmetic.residueChar w = p),
        (Arithmetic.inertDeg w : ℝ) / Module.finrank ℚ D.F *
          (if hw : w ∈ Iut.badPlacesOver D.F D.E D.VBad then
            (D.prime.qOrder w hw : ℝ) / (2 * (D.prime.ℓ : ℝ))
          else 0) := by
      simp [c]

end IutTorsionQRootSource

end

end JoshiTeich.Act1Scene1
