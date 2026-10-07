import ArithmeticTeichmullerSpaces.Act1Scene1.IutQPilotCompletionSource
import Iut.Cor312.ThetaData.AdmissiblePrime
import Iut.Cor312.ThetaData.BadPlaceNorm
import Iut.Cor312.ThetaData.Basic

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField
open TateCurvesTheta
open scoped NumberField

universe uF

/-!
source-id: IUT-COR312-REAL-ADMISSIBLE-PRIME-QPILOT
source: `iut`: `refer/iut/Iut/Cor312/ThetaData/Basic.lean`,
`InitialThetaData.prime`; `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`,
`AdmissiblePrimeData.tate`, `unif`, `unif_isUniformizer`, `q_order_coprime`, and
`qOrder`; `refer/iut/.lake/packages/tate-curves-theta/TateCurvesTheta/QParameter/NormalizedOrder.lean`,
`norm_q_eq_pow_orderNat` and `toOrdered_primeToOrder_iff`.
fidelity: constructs the base completion source and its normalized-order valuation
from the actual IUT admissible-prime fields, with an entry point fixed to the prime
inside actual `InitialThetaData`. Identification with a Scene1 link's prime, place
carrier, Tate parameter, and q-norm compatibility remains explicit.
boundary: Scene1/Derived
-/

variable {F : Type uF} [Field F] [NumberField F]
variable {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type uF} [Field Fbar] [Algebra F Fbar]
variable {VBad : Set (FinitePlace ↥(Iut.fieldOfModuli F E))}

/-- The actual IUT base-field q-pilot carrier and Tate parameters. -/
noncomputable def IutBaseQPilotSource.ofAdmissiblePrimeData
    (ell : ℕ) (P : Iut.AdmissiblePrimeData F E Fbar VBad)
    (hBadFinite : (Iut.badPlacesOver F E VBad).Finite) :
    IutBaseQPilotSource F ell := by
  refine
    { badPlaces := Iut.badPlacesOver F E VBad
      badFinset := hBadFinite.toFinset
      badFinset_spec := hBadFinite.coe_toFinset
      weight := Arithmetic.qPilotWeight
      weight_eq_qPilotWeight := fun _ => rfl
      tateParameter := fun w =>
        (P.tate w.1 (hBadFinite.mem_toFinset.mp w.2)).q
      tateParameter_ne_zero := ?_
      tateParameter_norm_lt_one := ?_ }
  · intro w
    exact (P.tate w.1 (hBadFinite.mem_toFinset.mp w.2)).q.ne_zero
  · intro w
    exact (P.tate w.1 (hBadFinite.mem_toFinset.mp w.2)).norm_lt_one

namespace IutQPilotSource

variable {O : Type uF} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data F O p}

private lemma admissibleBadPlaces_finite_of_link
    (hPlaces : Iut.badPlacesOver F E VBad =
      (↑T.scene1.data.link.places : Set (FinitePlace F))) :
    (Iut.badPlacesOver F E VBad).Finite := by
  rw [hPlaces]
  exact T.scene1.data.link.places.finite_toSet

/-- A local Scene1 parameter, packaged as a Tate parameter using the existing
nonzero and norm laws. -/
private noncomputable def sceneLinkTateParameter
    {O : Type uF} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data F O p}
    (w : FinitePlace F) (hw : w ∈ T.scene1.data.link.tate.places) :
    TateParameter (Iut.localCompletion w) :=
  TateParameter.ofNormLtOne
    (T.scene1.input_laws.tate_parameter.parameter_nonzero w hw)
    (by
      rw [← T.scene1.input_laws.tate_parameter.norm_eq w hw]
      exact T.scene1.input_laws.tate_parameter.norm_lt_one w hw)

/-- The IUT `tateJ_eq` field and the reference project's `q ↦ j(E_q)` injectivity
identify a Scene1 parameter once both parameters are known to represent `E`. -/
theorem initialThetaParameter_eq_of_tateJ
    {AG : Iut.AnabelianGeometry.{uF}}
    {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG)
    {O : Type uF} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data D.F O p}
    (hPlaces : Iut.badPlacesOver D.F D.E D.VBad =
      (↑T.scene1.data.link.places : Set (FinitePlace D.F)))
    (hCompat : QNormTateCompatibility T.scene1.data.link)
    (hLinkTateJ : ∀ w (hw : w ∈ T.scene1.data.link.tate.places),
      (sceneLinkTateParameter p w hw).tateJ =
        FinitePlace.embedding w.maximalIdeal D.E.j) :
    ∀ w : (IutBaseQPilotSource.ofAdmissiblePrimeData T.ell D.prime
      (admissibleBadPlaces_finite_of_link p hPlaces)).badFinset,
      ((D.prime.tate w.1
        (((admissibleBadPlaces_finite_of_link p hPlaces).mem_toFinset).mp w.2)).q :
          w.1.maximalIdeal.adicCompletion D.F) =
        T.scene1.data.link.tate.parameter w.1 := by
  intro w
  let hBadFinite := admissibleBadPlaces_finite_of_link p hPlaces
  have hwBad : w.1 ∈ Iut.badPlacesOver D.F D.E D.VBad :=
    hBadFinite.mem_toFinset.mp w.2
  have hwPlaces : w.1 ∈ (↑T.scene1.data.link.places : Set (FinitePlace D.F)) := by
    rw [← hPlaces]
    exact hwBad
  have hwLink : w.1 ∈ T.scene1.data.link.places := by
    exact Finset.mem_coe.mp hwPlaces
  have hwTate : w.1 ∈ T.scene1.data.link.tate.places := by
    rw [← hCompat.places_eq]
    exact hwLink
  let tLink := sceneLinkTateParameter p w.1 hwTate
  let tIut := D.prime.tate w.1 hwBad
  have htateJ : tLink.tateJ = tIut.tateJ := by
    rw [hLinkTateJ w.1 hwTate, D.prime.tateJ_eq w.1 hwBad]
  have hTateEq : tLink = tIut :=
    TateParameter.tateJ_injective tLink tIut (Iut.twelve_ne_zero w.1) htateJ
  have hq : (tLink.q : Iut.localCompletion w.1) =
      (tIut.q : Iut.localCompletion w.1) := congrArg
        (fun t : TateParameter (Iut.localCompletion w.1) =>
          (t.q : Iut.localCompletion w.1)) hTateEq
  have hq' : T.scene1.data.link.tate.parameter w.1 =
      (tIut.q : Iut.localCompletion w.1) := by
    simpa [tLink, sceneLinkTateParameter, Iut.localCompletion] using hq
  exact hq'.symm

/-- Assemble `IutQPilotSource` from the real IUT admissible-prime datum.

The source q-order, its positivity, its coprimality, and the chosen-uniformizer
norm law are derived from `P.tate`, `P.unif`, and `P.q_order_coprime`. The two
remaining identifications say that this base-field q-pilot is the one carried
by the Scene1 link.
-/
noncomputable def ofAdmissiblePrimeData
    (P : Iut.AdmissiblePrimeData F E Fbar VBad)
    (hEll : T.ell = P.ℓ)
    (hPlaces : Iut.badPlacesOver F E VBad =
      (↑T.scene1.data.link.places : Set (FinitePlace F)))
    (hParameter : ∀ w :
      (IutBaseQPilotSource.ofAdmissiblePrimeData T.ell P
        (admissibleBadPlaces_finite_of_link p hPlaces)).badFinset,
      ((P.tate w.1
        (((admissibleBadPlaces_finite_of_link p hPlaces).mem_toFinset).mp w.2)).q :
        w.1.maximalIdeal.adicCompletion F) =
        T.scene1.data.link.tate.parameter w.1)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    IutQPilotSource p T := by
  let hBadFinite : (Iut.badPlacesOver F E VBad).Finite :=
    admissibleBadPlaces_finite_of_link p hPlaces
  let B : IutBaseQPilotSource F T.ell :=
    IutBaseQPilotSource.ofAdmissiblePrimeData T.ell P hBadFinite
  let C : IutCompletionTateValuation B := by
    refine IutCompletionTateValuation.ofIutNormalizedOrder
      (uniformizer := fun w => P.unif w.1 (B.mem_badPlaces w))
      (hUniformizer := ?_)
      (sourceOrder := fun w => P.qOrder w.1 (B.mem_badPlaces w))
      (sourceOrder_norm_eq := ?_)
      (sourceOrder_coprime := ?_)
    · intro w
      let hπ := P.unif_isUniformizer w.1 (B.mem_badPlaces w)
      exact ⟨hπ.ne_zero, hπ.norm_lt_one, hπ.generates⟩
    · intro w
      let hw := B.mem_badPlaces w
      change ‖((P.tate w.1 hw).q :
        w.1.maximalIdeal.adicCompletion F)‖ =
        ‖P.unif w.1 hw‖ ^ P.qOrder w.1 hw
      exact (P.tate w.1 hw).norm_q_eq_pow_orderNat
        (P.unif_isUniformizer w.1 hw)
    · intro w
      let hw := B.mem_badPlaces w
      have hcop : Nat.Coprime P.ℓ (P.qOrder w.1 hw) := by
        change Nat.Coprime P.ℓ
          ((P.tate w.1 hw).toOrdered (P.unif_isUniformizer w.1 hw)).orderNat
        exact ((P.tate w.1 hw).toOrdered_primeToOrder_iff
          (P.unif_isUniformizer w.1 hw) P.ℓ).mp (P.q_order_coprime w.1 hw)
      simpa only [hEll] using hcop
  exact IutQPilotSource.ofBaseCompletionSource p B C hPlaces hParameter hCompat

/-- Assemble the q-pilot source from the admissible-prime projection of actual
IUT initial Theta-data. The prime source is fixed to `D.prime`; the target-prime,
place, local-parameter, and q-norm/Tate identifications remain explicit.
-/
noncomputable def ofInitialThetaData
    {AG : Iut.AnabelianGeometry.{uF}}
    {TG : Iut.TemperedGeometry AG}
    (D : Iut.InitialThetaData AG TG)
    {O : Type uF} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data D.F O p}
    (hEll : T.ell = D.prime.ℓ)
    (hPlaces : Iut.badPlacesOver D.F D.E D.VBad =
      (↑T.scene1.data.link.places : Set (FinitePlace D.F)))
    (hLinkTateJ : ∀ w (hw : w ∈ T.scene1.data.link.tate.places),
      (sceneLinkTateParameter p w hw).tateJ =
        FinitePlace.embedding w.maximalIdeal D.E.j)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    IutQPilotSource p T := by
  have hParameter :=
    initialThetaParameter_eq_of_tateJ D p hPlaces hCompat hLinkTateJ
  exact ofAdmissiblePrimeData p D.prime hEll hPlaces hParameter hCompat

end IutQPilotSource

end JoshiTeich.Act1Scene1
