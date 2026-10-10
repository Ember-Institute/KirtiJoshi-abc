import ArithmeticTeichmullerSpaces.Act1Scene1.IutQPilotCompletionSource
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBadPlaceFiniteness
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBaseQPilotSource
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.AdmissiblePrime
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.BadPlaceNorm
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.Basic

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
variable {VBad : Set (FinitePlace ↥(JoshiTeich.ReferenceIut.fieldOfModuli F E))}

namespace IutQPilotSource

variable {O : Type uF} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {T : Corollary312Data F O p}

private lemma tateParameter_eq_of_q_eq
    {K : Type uF} [NormedField K] {t₁ t₂ : TateParameter K}
    (h : (t₁.q : K) = (t₂.q : K)) : t₁ = t₂ := by
  cases t₁
  cases t₂
  simp only [TateParameter.mk.injEq]
  exact Units.ext h

private lemma admissibleBadPlaces_finite_of_link
    (hPlaces : JoshiTeich.ReferenceIut.badPlacesOver F E VBad =
      (↑T.scene1.data.link.places : Set (FinitePlace F))) :
    (JoshiTeich.ReferenceIut.badPlacesOver F E VBad).Finite := by
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
    TateParameter (JoshiTeich.ReferenceIut.localCompletion w) :=
  TateParameter.ofNormLtOne
    (T.scene1.input_laws.tate_parameter.parameter_nonzero w hw)
    (by
      rw [← T.scene1.input_laws.tate_parameter.norm_eq w hw]
      exact T.scene1.input_laws.tate_parameter.norm_lt_one w hw)

/-- The IUT `tateJ_eq` field and the reference project's `q ↦ j(E_q)` injectivity
identify a Scene1 parameter once both parameters are known to represent `E`. -/
theorem initialThetaParameter_eq_of_tateJ
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{uF}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {O : Type uF} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data D.F O p}
    (hPlaces : JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad =
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
  have hwBad : w.1 ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
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
    TateParameter.tateJ_injective tLink tIut (JoshiTeich.ReferenceIut.twelve_ne_zero w.1) htateJ
  have hq : (tLink.q : JoshiTeich.ReferenceIut.localCompletion w.1) =
      (tIut.q : JoshiTeich.ReferenceIut.localCompletion w.1) := congrArg
        (fun t : TateParameter (JoshiTeich.ReferenceIut.localCompletion w.1) =>
          (t.q : JoshiTeich.ReferenceIut.localCompletion w.1)) hTateEq
  have hq' : T.scene1.data.link.tate.parameter w.1 =
      (tIut.q : JoshiTeich.ReferenceIut.localCompletion w.1) := by
    simpa [tLink, sceneLinkTateParameter, JoshiTeich.ReferenceIut.localCompletion] using hq
  exact hq'.symm

/-- Assemble `IutQPilotSource` from the real IUT admissible-prime datum.

The source q-order, its positivity, its coprimality, and the chosen-uniformizer
norm law are derived from `P.tate`, `P.unif`, and `P.q_order_coprime`. The two
remaining identifications say that this base-field q-pilot is the one carried
by the Scene1 link.
-/
noncomputable def ofAdmissiblePrimeData
    (P : JoshiTeich.ReferenceIut.AdmissiblePrimeData F E Fbar VBad)
    (hEll : T.ell = P.ℓ)
    (hPlaces : JoshiTeich.ReferenceIut.badPlacesOver F E VBad =
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
  let hBadFinite : (JoshiTeich.ReferenceIut.badPlacesOver F E VBad).Finite :=
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
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{uF}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {O : Type uF} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data D.F O p}
    (hEll : T.ell = D.prime.ℓ)
    (hPlaces : JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad =
      (↑T.scene1.data.link.places : Set (FinitePlace D.F)))
    (hLinkTateJ : ∀ w (hw : w ∈ T.scene1.data.link.tate.places),
      (sceneLinkTateParameter p w hw).tateJ =
        FinitePlace.embedding w.maximalIdeal D.E.j)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    IutQPilotSource p T := by
  have hParameter :=
    initialThetaParameter_eq_of_tateJ D p hPlaces hCompat hLinkTateJ
  exact ofAdmissiblePrimeData p D.prime hEll hPlaces hParameter hCompat

/-!
The q-pilot source uses only the finite carrier and the local Tate parameter
fields of a Scene1 link.  This constructor exposes that smaller source
boundary: the full `AdelicThetaLinkData` equality is not needed.  The
parameter-to-`j` identification is derived from the actual admissible-prime
`tateJ_eq` field and injectivity of the Tate parameter's `j` map.
-/
noncomputable def ofInitialThetaData_of_parameter_eq
    {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{uF}}
    {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    {O : Type uF} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    {T : Corollary312Data D.F O p}
    (hEll : T.ell = D.prime.ℓ)
    (hPlaces : JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad =
      (↑T.scene1.data.link.places : Set (FinitePlace D.F)))
    (hParameter : ∀ w : (IutBaseQPilotSource.ofInitialThetaData D).badFinset,
      (IutBaseQPilotSource.ofInitialThetaData D).tateParameter w =
        T.scene1.data.link.tate.parameter w.1)
    (hCompat : QNormTateCompatibility T.scene1.data.link) :
    IutQPilotSource p T := by
  let hBadFinite := iutInitialThetaBadPlacesOver_finite D
  let B := IutBaseQPilotSource.ofInitialThetaData D
  have hLinkTateJ : ∀ w (hw : w ∈ T.scene1.data.link.tate.places),
      (sceneLinkTateParameter p w hw).tateJ =
        FinitePlace.embedding w.maximalIdeal D.E.j := by
    intro w hw
    have hwLink : w ∈ T.scene1.data.link.places := by
      rw [hCompat.places_eq]
      exact hw
    have hwBad : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := by
      rw [hPlaces]
      exact Finset.mem_coe.mpr hwLink
    have hwB : w ∈ B.badFinset := by
      change w ∈ hBadFinite.toFinset
      exact hBadFinite.mem_toFinset.mpr hwBad
    let tLink := sceneLinkTateParameter p w hw
    let tIut := D.prime.tate w hwBad
    have hq : (tLink.q : JoshiTeich.ReferenceIut.localCompletion w) =
        (tIut.q : JoshiTeich.ReferenceIut.localCompletion w) := by
      change T.scene1.data.link.tate.parameter w =
        (IutBaseQPilotSource.ofInitialThetaData D).tateParameter ⟨w, hwB⟩
      rw [hParameter ⟨w, hwB⟩]
    have hTateEq : tLink = tIut := tateParameter_eq_of_q_eq hq
    calc
      tLink.tateJ = tIut.tateJ := congrArg TateParameter.tateJ hTateEq
      _ = FinitePlace.embedding w.maximalIdeal D.E.j :=
        D.prime.tateJ_eq w hwBad
  exact ofInitialThetaData D p hEll hPlaces hLinkTateJ hCompat

end IutQPilotSource

end JoshiTeich.Act1Scene1
