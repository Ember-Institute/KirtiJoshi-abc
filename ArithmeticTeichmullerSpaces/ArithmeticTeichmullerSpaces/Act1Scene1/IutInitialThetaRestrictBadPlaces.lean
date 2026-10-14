import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.Basic

/-!
source-id: JT-SCENE1-INITIAL-THETA-RESTRICT-BAD-PLACES
source: the actual InitialThetaData global/prime/Tate/orbicurve/local fields.
fidelity: constructs full InitialThetaData on any nonempty subset of its
chosen bad places. All local bad-place obligations are restricted; fields,
curve, torsion representation, section and covering data are retained.
This proves closure under restriction, not existence of initial theta data.
Original reconstruction; no reference code is copied or imported externally.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.InitialThetaRestriction
open JoshiTeich.ReferenceIut NumberField JoshiTeich.ReferenceIut.OrbicurveDataSection
universe u
noncomputable section
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (D : InitialThetaData AG TG)
variable (W : Set (FinitePlace ↥(fieldOfModuli D.F D.E))) (hW : W ⊆ D.VBad)

include hW in
private theorem badOver_mono {w : FinitePlace D.F} (hw : w ∈ badPlacesOver D.F D.E W) :
    w ∈ badPlacesOver D.F D.E D.VBad := by
  obtain ⟨v, hv, hwv⟩ := hw
  exact ⟨v, hW hv, hwv⟩

private def prime : AdmissiblePrimeData D.F D.E D.Fbar W where
  ℓ := D.prime.ℓ
  ℓ_prime := D.prime.ℓ_prime
  five_le := D.prime.five_le
  torsionBasis := D.prime.torsionBasis
  rep := D.prime.rep
  rep_spec := D.prime.rep_spec
  sl_le_range := D.prime.sl_le_range
  ker_isOpen := D.prime.ker_isOpen
  galois_deg_prime := D.prime.galois_deg_prime
  residueChar_coprime v hv := D.prime.residueChar_coprime v (hW hv)
  tate w hw := D.prime.tate w (badOver_mono D W hW hw)
  tateJ_eq w hw := D.prime.tateJ_eq w (badOver_mono D W hW hw)
  unif w hw := D.prime.unif w (badOver_mono D W hW hw)
  unif_isUniformizer w hw := D.prime.unif_isUniformizer w (badOver_mono D W hW hw)
  q_order_coprime w hw := D.prime.q_order_coprime w (badOver_mono D W hW hw)

local instance restrictedNumberField : NumberField ↥(prime D W hW).torsionField := D.numberFieldK
local instance restrictedModuliAlgebra :
    Algebra ↥(fieldOfModuli D.F D.E) ↥(prime D W hW).torsionField := D.algebraModK

private def orb : OrbicurveData AG D.F D.E D.Fbar W (prime D W hW) where
  CKu := D.orb.CKu
  CKu_type := D.orb.CKu_type
  CKu_core := D.orb.CKu_core
  XKu := D.orb.XKu
  XKu_type := D.orb.XKu_type
  XKu_to_XK := D.orb.XKu_to_XK
  XKu_to_CKu := D.orb.XKu_to_CKu
  XK_to_CK := D.orb.XK_to_CK
  CKu_to_CK := D.orb.CKu_to_CK
  diagram_cartesian := D.orb.diagram_cartesian
  QIso := D.orb.QIso
  q := D.orb.q
  q_ne_zero := D.orb.q_ne_zero
  epsilon := D.orb.epsilon
  epsilon_spec := D.orb.epsilon_spec

private def valuationSection : ValuationSection D.F D.E D.Fbar W (prime D W hW) where
  sectFin := D.localData.sect.sectFin
  sectInf := D.localData.sect.sectInf
  sectFin_liesOver := D.localData.sect.sectFin_liesOver
  sectInf_liesOver := D.localData.sect.sectInf_liesOver

private def localData : LocalThetaData AG TG D.F D.E D.Fbar W (prime D W hW) (orb D W hW) where
  sect := valuationSection D W hW
  local_diagram_cartesian := D.localData.local_diagram_cartesian
  decomp := D.localData.decomp
  decomp_isClosed := D.localData.decomp_isClosed
  tateX v hv := D.localData.tateX v (hW hv)
  tateC v hv := D.localData.tateC v (hW hv)
  bad_type v hv := D.localData.bad_type v (hW hv)
  bad_theta_model v hv := D.localData.bad_theta_model v (hW hv)
  epsilon_graph v hv := D.localData.epsilon_graph v (hW hv)

private def tate : TateFamily D.E (prime D W hW).torsionField (prime D W hW).ℓ W where
  S w hw := D.tate.S w (by obtain ⟨v, hv, hwv⟩ := hw; exact ⟨v, hW hv, hwv⟩)
  graphLine_galPlace w hw σ := D.tate.graphLine_galPlace w
    (by obtain ⟨v, hv, hwv⟩ := hw; exact ⟨v, hW hv, hwv⟩) σ
  isCanonical_galPlace w hw σ R := D.tate.isCanonical_galPlace w
    (by obtain ⟨v, hv, hwv⟩ := hw; exact ⟨v, hW hv, hwv⟩) σ R

def restrict (hne : W.Nonempty) : InitialThetaData AG TG where
  F := D.F
  fieldF := D.fieldF
  numberFieldF := D.numberFieldF
  Fbar := D.Fbar
  fieldFbar := D.fieldFbar
  algebraFbar := D.algebraFbar
  isAlgClosure := D.isAlgClosure
  E := D.E
  isElliptic := D.isElliptic
  VBad := W
  global :=
    { sqrt_neg_one := D.global.sqrt_neg_one
      stable_reduction := D.global.stable_reduction
      six_torsion_rational := D.global.six_torsion_rational
      bad_nonempty := hne
      bad_odd := fun v hv => D.global.bad_odd v (hW hv)
      bad_multiplicative := fun v hv => D.global.bad_multiplicative v (hW hv) }
  prime := prime D W hW
  numberFieldK := D.numberFieldK
  algebraModK := D.algebraModK
  towerModK := D.towerModK
  tate := tate D W hW
  orb := orb D W hW
  localData := localData D W hW

theorem restrict_VBad (hne : W.Nonempty) : (restrict D W hW hne).VBad = W := rfl
theorem restrict_rep (hne : W.Nonempty) : (restrict D W hW hne).prime.rep = D.prime.rep := rfl
theorem restrict_section (hne : W.Nonempty) :
    (restrict D W hW hne).localData.sect.sectFin = D.localData.sect.sectFin := rfl

end
end JoshiTeich.Act1Scene1.InitialThetaRestriction
