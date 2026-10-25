/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.ProducerContracts
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaValuationSection

namespace JoshiTeich.Act1Scene1

open JoshiTeich.ReferenceIut
open JoshiTeich.ReferenceIut.OrbicurveDataSection
open NumberField

universe u

noncomputable section

/-!
source-id: JT-SCENE1-INITIAL-THETA-REFERENCE-ANABELIAN-EXISTENCE-ADAPTER
source: `refer/iut/Iut/Concrete/Existence.lean`, `AnabelianExistence`,
IUT I Definition 3.1(d)--(f), and IUT IV Corollary 2.2 proof (P7).
fidelity: ports only the reference existential contract and adapts it to the
independent `InitialThetaGeometryProducer` seed. No reference model geometry
or existence proof is imported, and no inhabitant of this contract is added.
boundary: Scene1/Derived. The contract remains an explicit source obligation;
the adapter does not prove universal anabelian existence.
-/

/-- The reference工程's anabelian existence contract, stated over the
arithmetic and Tate inputs rather than over the combined Scene1 seed. -/
structure ReferenceAnabelianExistenceContract
    (AG : AnabelianGeometry.{u}) (TG : TemperedGeometry AG) : Prop where
  exists_data :
    ∀ (F : Type u) [Field F] [NumberField F]
      (E : WeierstrassCurve F) [E.IsElliptic]
      (Fbar : Type u) [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
      (VBad : Set (FinitePlace ↥(fieldOfModuli F E)))
      (P : AdmissiblePrimeData F E Fbar VBad)
      [NumberField ↥P.torsionField]
      (TF : TateFamily E P.torsionField P.ℓ VBad),
      IsInitialThetaGlobalData F E Fbar VBad →
      HasCoreUniversally AG F E →
      ∃ O : OrbicurveData AG F E Fbar VBad P,
        Nonempty (LocalThetaData AG TG F E Fbar VBad P O)

namespace ReferenceAnabelianExistenceContract

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- Adapt the reference contract to the combined arithmetic/Tate seed. -/
def toInitialThetaGeometryProducer
    (A : ReferenceAnabelianExistenceContract AG TG) :
    InitialThetaGeometryProducer AG TG where
  produce S :=
    S.algebraModK_eq_canonical.symm ▸
      A.exists_data S.F S.E S.Fbar S.VBad S.prime S.tate S.global S.core

theorem toInitialThetaGeometryProducer_produce
    (A : ReferenceAnabelianExistenceContract AG TG)
    (S : InitialThetaGeometrySeed AG TG) :
    ∃ O : OrbicurveData AG S.F S.E S.Fbar S.VBad S.prime,
      Nonempty (LocalThetaData AG TG S.F S.E S.Fbar S.VBad S.prime O) := by
  exact S.algebraModK_eq_canonical.symm ▸
    A.exists_data S.F S.E S.Fbar S.VBad S.prime S.tate S.global S.core

end ReferenceAnabelianExistenceContract

end
end JoshiTeich.Act1Scene1
