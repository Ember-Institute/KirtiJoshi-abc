import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTiltAlgebraicallyClosed

/-!
source-id: JT-SCENE1-INITIAL-THETA-TILT-INTEGERS
source: Joshi II canonical W(O_F) source before pr:teichmuller-lift-A;
the actual PreTilt inclusion, unit-ball identity and sharp norm producers.
fidelity: identifies the original PreTilt with the actual tilt valuation
integer ring by an isometric ring equivalence. Restricts the same sharp to
the actual untilt integers. No integral-ring or equivalence certificate is
input. Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTiltIntegers

open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance primeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w

/-- The valuation integers of the existing actual tilt, with its existing norm. -/
abbrev Integers := LocalGeometricFontaine.integerRing (InitialThetaTiltField.Carrier D w)

def inclusion : InitialThetaTiltField.Source D w →+* Integers D w :=
  (InitialThetaTiltField.inclusion D w).codRestrict _ fun x =>
    (LocalGeometricFontaine.mem_integerRing _ _).mpr (by
      rw [InitialThetaPreTiltCompleteness.inclusion_norm]
      exact InitialThetaTiltCompleteness.source_norm_le_one D w x)

theorem inclusion_coe (x : InitialThetaTiltField.Source D w) :
    (inclusion D w x : InitialThetaTiltField.Carrier D w) =
      InitialThetaTiltField.inclusion D w x := rfl

theorem inclusion_bijective : Function.Bijective (inclusion D w) := by
  constructor
  · intro x y h
    exact InitialThetaTiltField.inclusion_injective D w (congrArg Subtype.val h)
  · intro x
    obtain ⟨y, hy⟩ := InitialThetaTiltCompleteness.norm_le_one_mem_range D w
      (x : InitialThetaTiltField.Carrier D w) ((LocalGeometricFontaine.mem_integerRing _ _).mp x.property)
    exact ⟨y, Subtype.ext hy⟩

/-- Surjectivity uses the proved equality of the PreTilt image and the actual unit ball. -/
def preTiltEquiv : InitialThetaTiltField.Source D w ≃+* Integers D w :=
  RingEquiv.ofBijective (inclusion D w) (inclusion_bijective D w)

theorem preTiltEquiv_coe (x : InitialThetaTiltField.Source D w) :
    (preTiltEquiv D w x : InitialThetaTiltField.Carrier D w) =
      InitialThetaTiltField.inclusion D w x := rfl

theorem preTiltEquiv_symm_coe (x : Integers D w) :
    InitialThetaTiltField.inclusion D w ((preTiltEquiv D w).symm x) =
      (x : InitialThetaTiltField.Carrier D w) :=
  congrArg Subtype.val ((preTiltEquiv D w).apply_symm_apply x)

theorem preTiltEquiv_isometry : Isometry (preTiltEquiv D w) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  exact (InitialThetaPreTiltCompleteness.inclusion_isometry D w).dist_eq x y

theorem preTiltEquiv_norm (x : InitialThetaTiltField.Source D w) :
    ‖preTiltEquiv D w x‖ = ‖x‖ := InitialThetaPreTiltCompleteness.inclusion_norm D w x

/-- Integral sharp is multiplicative; no cross-characteristic additive map is asserted. -/
def sharp : Integers D w →*₀
    LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w) where
  toFun x := ⟨InitialThetaTiltSharp.sharp D w x,
    (LocalGeometricFontaine.mem_integerRing _ _).mpr (by
      rw [InitialThetaTiltTopology.norm_sharp]
      exact (LocalGeometricFontaine.mem_integerRing _ _).mp x.property)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

theorem sharp_norm (x : Integers D w) : ‖sharp D w x‖ = ‖x‖ :=
  InitialThetaTiltTopology.norm_sharp D w x

theorem sharp_preTiltEquiv (x : InitialThetaTiltField.Source D w) :
    sharp D w (preTiltEquiv D w x) =
      (InitialThetaCanonicalGeometricFontaine.placeData D w).data.untilt x := by
  apply Subtype.ext
  exact InitialThetaTiltSharp.sharp_inclusion D w x

theorem sharp_surjective : Function.Surjective (sharp D w) := by
  intro z
  obtain ⟨x, hx⟩ := InitialThetaTiltSharp.sharp_surjective D w z
  have hbound : ‖x‖ ≤ 1 := by
    rw [← InitialThetaTiltTopology.norm_sharp D w x, hx]
    exact (LocalGeometricFontaine.mem_integerRing _ _).mp z.property
  exact ⟨⟨x, (LocalGeometricFontaine.mem_integerRing _ _).mpr hbound⟩, Subtype.ext hx⟩

end
end JoshiTeich.Act1Scene1.InitialThetaTiltIntegers
