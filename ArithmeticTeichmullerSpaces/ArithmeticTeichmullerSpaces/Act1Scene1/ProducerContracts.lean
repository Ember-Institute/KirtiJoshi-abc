import ArithmeticTeichmullerSpaces.Act1Scene1.Boundary
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Cor312.ThetaData.Basic

namespace JoshiTeich.Act1Scene1

open JoshiTeich.ReferenceIut
open NumberField
open JoshiTeich.ReferenceIut.OrbicurveDataSection

universe u

/-!
source-id: JT-SCENE1-PRODUCER-CONTRACTS
source: IUT I, Definition 3.1; `refer/iut/Iut/Concrete/Existence.lean`,
`AnabelianExistence` and `EllipticCurveData.thetaData`; Joshi II--III
holomorphoid, untilt, theta-value, and collation constructions.
fidelity: explicit Scene1 producer contracts.  These structures record the
missing source obligations without promoting them to Prologue/Core and without
storing Corollary 3.12 or an equivalent inequality.
boundary: Scene1/Derived

The four stages are intentionally separate.  The first stage produces the
anabelian part of initial Theta-data.  The next stages consume the same data
and expose the analytic, cohomological, and paper-collation obligations.  A
field named `law` is a genuine explicit proposition supplied by a producer;
there is no default constructor for these laws.
-/

/-! ## Scene1-A: geometric Initial-Theta producer -/

/-- The non-anabelian seed consumed by a geometric Initial-Theta producer. -/
structure InitialThetaGeometrySeed
    (AG : AnabelianGeometry.{u}) (TG : TemperedGeometry AG) where
  F : Type u
  [fieldF : Field F]
  [numberFieldF : NumberField F]
  Fbar : Type u
  [fieldFbar : Field Fbar]
  [algebraFbar : Algebra F Fbar]
  [isAlgClosure : IsAlgClosure F Fbar]
  E : WeierstrassCurve F
  [isElliptic : E.IsElliptic]
  VBad : Set (NumberField.FinitePlace ↥(fieldOfModuli F E))
  global : IsInitialThetaGlobalData F E Fbar VBad
  prime : AdmissiblePrimeData F E Fbar VBad
  [numberFieldK : NumberField ↥prime.torsionField]
  [algebraModK : Algebra ↥(fieldOfModuli F E) ↥prime.torsionField]
  [towerModK : @IsScalarTower ↥(fieldOfModuli F E) F ↥prime.torsionField
    (inferInstance : SMul ↥(fieldOfModuli F E) F)
    (inferInstance : SMul F ↥prime.torsionField)
    algebraModK.toSMul]
  tate : TateFamily E prime.torsionField prime.ℓ VBad
  core : OrbicurveDataSection.HasCoreUniversally AG F E

attribute [instance] InitialThetaGeometrySeed.fieldF
  InitialThetaGeometrySeed.numberFieldF InitialThetaGeometrySeed.fieldFbar
  InitialThetaGeometrySeed.algebraFbar InitialThetaGeometrySeed.isAlgClosure
  InitialThetaGeometrySeed.isElliptic InitialThetaGeometrySeed.numberFieldK
  InitialThetaGeometrySeed.algebraModK InitialThetaGeometrySeed.towerModK

/--
The missing geometric producer.  Its output is exactly the `orb` and
`localData` part of `InitialThetaData`; the seed contains the arithmetic and
Tate fields and the producer must supply the anabelian/local existence
witness.  This is the explicit Scene1 counterpart of the reference
`AnabelianExistence` contract.
-/
structure InitialThetaGeometryProducer
    (AG : AnabelianGeometry.{u}) (TG : TemperedGeometry AG) : Type (u + 1) where
  produce : ∀ (S : InitialThetaGeometrySeed AG TG),
    ∃ O : OrbicurveData AG S.F S.E S.Fbar S.VBad S.prime,
      Nonempty (LocalThetaData AG TG S.F S.E S.Fbar S.VBad S.prime O)

namespace InitialThetaGeometryProducer

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- Assemble the produced witness into the reference `InitialThetaData`.
This is conditional on an explicit `InitialThetaGeometryProducer`; it is not
available from the Prologue input bundle alone.
-/
noncomputable def toInitialThetaData
    (P : InitialThetaGeometryProducer AG TG)
    (S : InitialThetaGeometrySeed AG TG) : InitialThetaData AG TG := by
  let h := P.produce S
  exact
    { F := S.F
      Fbar := S.Fbar
      E := S.E
      VBad := S.VBad
      global := S.global
      prime := S.prime
      tate := S.tate
      orb := h.choose
      localData := h.choose_spec.some }

end InitialThetaGeometryProducer

/-! ## Scene1-B: holomorphoid and perfectoid source -/

/-- The explicit analytic carriers associated with one produced `D`. -/
structure HolomorphoidSource
    (AG : AnabelianGeometry.{u}) (TG : TemperedGeometry AG)
    (D : InitialThetaData AG TG) : Type (u + 1) where
  marking : Type u
  untilt : marking → Type u
  tilt : marking → Type u
  geometricBasePoint : marking → Type u
  tateParameter : marking → Type u
  untiltLaw : Prop
  tiltLaw : Prop
  basePointLaw : Prop
  tateParameterLaw : Prop

/-! ## Scene1-C: H¹ₑ/Bloch--Kato/period comparison source -/

/--
The cohomological comparison producer is kept independent of
`InitialThetaData`: its carriers and comparison maps are explicit, while the
identification with the paper's H¹ₑ/BK/period objects remains a supplied law.
-/
structure H1eBKPeriodSource
    (AG : AnabelianGeometry.{u}) (TG : TemperedGeometry AG)
    (D : InitialThetaData AG TG)
    (H : HolomorphoidSource AG TG D) : Type (u + 1) where
  ambientH1 : Type u
  h1eCarrier : Type u
  crystallineCarrier : Type u
  periodCarrier : Type u
  comparison : ambientH1 → h1eCarrier
  crystalline : h1eCarrier → crystallineCarrier
  blochKatoLog : h1eCarrier → periodCarrier
  h1eLaw : Prop
  comparisonLaw : Prop
  crystallineLaw : Prop
  periodLaw : Prop

/-! ## Scene1-D: paper representatives and collation -/

/--
The paper-collation producer supplies representatives, multiplicities, and
the theta-volume carrier after the holomorphoid and comparison stages.  The
volume law is deliberately a field: it cannot be inferred from an actual
packet/hull volume by type conversion.
-/
structure PaperCollationSource
    (AG : AnabelianGeometry.{u}) (TG : TemperedGeometry AG)
    (D : InitialThetaData AG TG)
    (H : HolomorphoidSource AG TG D)
    (C : H1eBKPeriodSource AG TG D H) : Type (u + 1) where
  paperCarrier : Type u
  representative : Type u
  representativeMap : representative → paperCarrier
  multiplicity : representative → ℕ
  weight : representative → ℝ
  thetaLocus : Set paperCarrier
  thetaVolume : ℝ
  representativeLaw : Prop
  multiplicityLaw : Prop
  weightLaw : Prop
  thetaLocusLaw : Prop
  thetaVolumeLaw : Prop

end JoshiTeich.Act1Scene1
