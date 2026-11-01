import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTiltFontaine

/-!
source-id: JT-SCENE1-INITIAL-THETA-PADIC-TILT-WITT-LOCALIZATION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`.
fidelity: records the Teichmuller compatibility of the existing actual
pretilt-to-Ainf Witt equivalence. A direct standard-C_p integer-ring Witt
map was tested but remains a kernel-conversion boundary; this module does
not claim that map, p-localization, bounded localization, rho norms, Frechet
completion, paper `B`, or H1e/BK identities. Original proof; no reference
implementation copied. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicTiltWittLocalization

open JoshiTeich.Prologue
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

local instance actualPrimeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 :
      InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 :
        InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w

theorem preTiltWittEquiv_teichmuller (x : InitialThetaTiltField.Source D w) :
    InitialThetaTiltFontaine.preTiltWittEquiv D w
        (WittVector.teichmuller (Arithmetic.residueChar w.1) x) =
      WittVector.teichmuller (Arithmetic.residueChar w.1)
        (InitialThetaTiltIntegers.preTiltEquiv D w x) := by
  change WittVector.map (InitialThetaTiltIntegers.preTiltEquiv D w).toRingHom
      (WittVector.teichmuller (Arithmetic.residueChar w.1) x) = _
  rw [WittVector.map_teichmuller]
  rfl

theorem preTiltWittEquiv_coeff (x : WittVector (Arithmetic.residueChar w.1)
    (InitialThetaTiltField.Source D w)) (n : ℕ) :
    (InitialThetaTiltFontaine.preTiltWittEquiv D w x).coeff n =
      InitialThetaTiltIntegers.preTiltEquiv D w (x.coeff n) := by
  change (WittVector.map (InitialThetaTiltIntegers.preTiltEquiv D w).toRingHom x).coeff n = _
  rw [WittVector.map_coeff]
  rfl

end
end JoshiTeich.Act1Scene1.InitialThetaPadicTiltWittLocalization
