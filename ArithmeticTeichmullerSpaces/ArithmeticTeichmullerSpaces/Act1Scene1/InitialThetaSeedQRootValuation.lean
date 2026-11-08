import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSeedQRootSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutQRootAccounting

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open JoshiTeich.ReferenceIut
open JoshiTeich.Prologue
open NumberField WeierstrassCurve
open scoped Classical BigOperators

universe u

noncomputable section

local instance (priority := 1100)
    {F Fbar : Type u} [Field F] [Field Fbar] [Algebra F Fbar]
    (K : IntermediateField F Fbar) : DecidableEq ↥K :=
  fun a b => Classical.propDecidable (a = b)

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-!
source-id: IUT-COR312-INITIAL-THETA-QROOT-ACCOUNTING
source: seed specialization of the completion valuation and q-root accounting;
`Cor312/ThetaData/AdmissiblePrime.lean`, `unif`, `unif_isUniformizer`,
`q_order_coprime`, `qOrder`; `Concrete/ThetaLocalConstruct/Ordp.lean` and
`Data.lean`, `sum_weight_ordp_qroot`; Joshi III `ss:theta-data-fixing2`.
fidelity: derives the valuation from the same seed's original uniformizer,
identifies its q-order, and computes the q-root order at the seed's selected
valuation section. The finite weighted identity consumes this valuation.
boundary: Scene1/Derived; the supplied VBad is retained. No geometry producer,
paper representative identity, holomorphoid, or volume law is introduced.
-/

/-- The base completion order is the order of the seed's original Tate parameter. -/
theorem baseQPilotSource_qOrder_eq_prime
    (S : InitialThetaGeometrySeed AG TG) (w : S.baseQPilotSource.badFinset) :
    S.baseQPilotSource.qOrder w =
      S.prime.qOrder w.1 (S.baseQPilotSource.mem_badPlaces w) := by
  let hw := S.baseQPilotSource.mem_badPlaces w
  let hπ := S.prime.unif_isUniformizer w.1 hw
  exact iutCompletionQOrder_eq_of_norm_eq_uniformizer_pow w.1
    (S.baseQPilotSource.tateParameter w)
    (S.baseQPilotSource.tateParameter_ne_zero w)
    (S.baseQPilotSource.tateParameter_norm_lt_one w)
    (S.prime.unif w.1 hw) ⟨hπ.ne_zero, hπ.norm_lt_one, hπ.generates⟩
    (S.prime.qOrder w.1 hw)
    ((S.prime.tate w.1 hw).norm_q_eq_pow_orderNat hπ)

/-- The valuation uses the seed's chosen uniformizer and its prime-to-ell order. -/
def completionTateValuation (S : InitialThetaGeometrySeed AG TG) :
    IutCompletionTateValuation S.baseQPilotSource := by
  let B := S.baseQPilotSource
  refine IutCompletionTateValuation.ofIutNormalizedOrder
    (uniformizer := fun w => S.prime.unif w.1 (B.mem_badPlaces w))
    (hUniformizer := ?_)
    (sourceOrder := fun w => S.prime.qOrder w.1 (B.mem_badPlaces w))
    (sourceOrder_norm_eq := ?_)
    (sourceOrder_coprime := ?_)
  · intro w
    let hπ := S.prime.unif_isUniformizer w.1 (B.mem_badPlaces w)
    exact ⟨hπ.ne_zero, hπ.norm_lt_one, hπ.generates⟩
  · intro w
    let hw := B.mem_badPlaces w
    change ‖((S.prime.tate w.1 hw).q :
      w.1.maximalIdeal.adicCompletion S.F)‖ =
      ‖S.prime.unif w.1 hw‖ ^ S.prime.qOrder w.1 hw
    exact (S.prime.tate w.1 hw).norm_q_eq_pow_orderNat
      (S.prime.unif_isUniformizer w.1 hw)
  · intro w
    let hw := B.mem_badPlaces w
    exact ((S.prime.tate w.1 hw).toOrdered_primeToOrder_iff
      (S.prime.unif_isUniformizer w.1 hw) S.prime.ℓ).mp
        (S.prime.q_order_coprime w.1 hw)

theorem completionTateValuation_order_eq_prime
    (S : InitialThetaGeometrySeed AG TG) (w : S.baseQPilotSource.badFinset) :
    S.completionTateValuation.orderedQOrder w =
      S.prime.qOrder w.1 (S.baseQPilotSource.mem_badPlaces w) :=
  (S.completionTateValuation.completionQOrder_eq_orderNat w).symm.trans
    (S.baseQPilotSource_qOrder_eq_prime w)

theorem baseQPilotSource_qOrder_pos
    (S : InitialThetaGeometrySeed AG TG) (w : S.baseQPilotSource.badFinset) :
    0 < S.baseQPilotSource.qOrder w := by
  rw [S.baseQPilotSource_qOrder_eq_prime w]
  exact S.prime.qOrder_pos w.1 (S.baseQPilotSource.mem_badPlaces w)

theorem baseQPilotSource_qOrder_coprime
    (S : InitialThetaGeometrySeed AG TG) (w : S.baseQPilotSource.badFinset) :
    Nat.Coprime S.prime.ℓ (S.baseQPilotSource.qOrder w) :=
  S.completionTateValuation.qOrder_coprime w

/-- Reindex the source root at the seed's actual chosen representative. -/
def selectedQRootPlace (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    S.torsionQRootSource.badFinset := by
  refine ⟨S.valuationSection.sectFin v, ?_⟩
  apply (mem_iutBadPlacesOverFinset_iff
    S.baseQPilotSource.badPlaces S.baseQPilotSource.badPlaces_finite _).mpr
  exact ⟨S.valuationSection_contractedPlace v,
    ⟨v, hv, S.valuationSection_contractedPlace_liesOver v⟩,
    iutPlaceUnder_liesOver (F := S.F) (Kt := ↥S.prime.torsionField)
      (S.valuationSection.sectFin v)⟩

theorem selectedQRootPlace_basePlace
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    (S.torsionQRootSource.basePlace (S.selectedQRootPlace v hv)).1 =
      S.valuationSection_contractedPlace v := by
  exact IutTorsionQRootSource.basePlaceOf_eq_placeUnder
    (B := S.baseQPilotSource) (S.selectedQRootPlace v hv)

/-- The selected root is measured by the original base Tate order and ramification. -/
theorem selectedQRoot_ordp_eq
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    Arithmetic.ordp (S.valuationSection.sectFin v)
      (S.torsionQRootSource.qroot (S.selectedQRootPlace v hv)) =
        (S.prime.qOrder (S.valuationSection_contractedPlace v)
          ⟨v, hv, S.valuationSection_contractedPlace_liesOver v⟩ : ℝ) /
            (2 * (S.prime.ℓ : ℝ) *
              Arithmetic.ramIdx (S.valuationSection_contractedPlace v)) := by
  let B := S.baseQPilotSource
  let R := S.torsionQRootSource
  let s := S.selectedQRootPlace v hv
  have h := IutTorsionQRootSource.canonical_qroot_ordp_eq_of_tateValuation
    S.completionTateValuation R.qroot R.qroot_pow_eq
    (by have h := S.prime.five_le; omega) s
  have hbase : (IutTorsionQRootSource.basePlaceOf (B := B) s).1 =
      S.valuationSection_contractedPlace v :=
    S.selectedQRootPlace_basePlace v hv
  change Arithmetic.ordp (S.valuationSection.sectFin v)
    (S.torsionQRootSource.qroot (S.selectedQRootPlace v hv)) = _ at h
  rw [S.baseQPilotSource_qOrder_eq_prime] at h
  simpa only [s, R, hbase] using h

theorem selectedQRoot_ordp_pos
    (S : InitialThetaGeometrySeed AG TG)
    (v : FinitePlace ↥(fieldOfModuli S.F S.E)) (hv : v ∈ S.VBad) :
    0 < Arithmetic.ordp (S.valuationSection.sectFin v)
      (S.torsionQRootSource.qroot (S.selectedQRootPlace v hv)) := by
  rw [S.selectedQRoot_ordp_eq v hv]
  apply div_pos
  · exact_mod_cast S.prime.qOrder_pos (S.valuationSection_contractedPlace v)
      ⟨v, hv, S.valuationSection_contractedPlace_liesOver v⟩
  · have hEll : (0 : ℝ) < S.prime.ℓ := by
      exact_mod_cast S.prime.ℓ_prime.pos
    have hRam : (0 : ℝ) < Arithmetic.ramIdx (S.valuationSection_contractedPlace v) := by
      exact_mod_cast Arithmetic.ramIdx_pos (S.valuationSection_contractedPlace v)
    exact mul_pos (mul_pos (by norm_num) hEll) hRam

/-- The existing weighted transfer consumes the valuation derived from the seed. -/
theorem qroot_weighted_fiber_eq_base
    (S : InitialThetaGeometrySeed AG TG) (p : ℕ)
    [Fintype {v : FinitePlace ↥S.prime.torsionField // Arithmetic.residueChar v = p}] :
    (∑ v : {v : FinitePlace ↥S.prime.torsionField // Arithmetic.residueChar v = p},
      Arithmetic.placeWeight v.1 *
        (if hv : v.1 ∈ S.torsionQRootSource.badFinset then
          Arithmetic.ordp v.1 (S.torsionQRootSource.qroot ⟨v.1, hv⟩) else 0)) =
      ∑ w ∈ S.baseQPilotSource.badFinset.filter (fun w => Arithmetic.residueChar w = p),
        Arithmetic.qPilotWeight w *
          (if hw : w ∈ S.baseQPilotSource.badPlaces then
            (S.prime.qOrder w hw : ℝ) / (2 * (S.prime.ℓ : ℝ)) else 0) := by
  let B := S.baseQPilotSource
  let R := S.torsionQRootSource
  let c : FinitePlace S.F → ℝ := fun w =>
    if hw : w ∈ B.badPlaces then
      (S.prime.qOrder w hw : ℝ) / (2 * (S.prime.ℓ : ℝ)) else 0
  have hc : ∀ w : B.badFinset,
      c w.1 = (B.qOrder w : ℝ) / (2 * (S.prime.ℓ : ℝ)) := by
    intro w
    rw [S.baseQPilotSource_qOrder_eq_prime]
    simp only [c, dite_eq_left (B.mem_badPlaces w)]
  exact IutTorsionQRootSource.canonical_qroot_weighted_sum_of_tateValuation
    p B.badFinset B.badFinset_spec c hc R.qroot R.qroot_pow_eq
      S.completionTateValuation (by have h := S.prime.five_le; omega)

end

end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
