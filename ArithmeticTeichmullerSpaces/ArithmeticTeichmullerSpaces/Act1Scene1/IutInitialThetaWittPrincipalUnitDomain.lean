import ArithmeticTeichmullerSpaces.Act1Scene1.UltrametricPrincipalUnits
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTateLogarithm

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-PRINCIPAL-UNIT-DOMAIN
source: Joshi II `se:ff-rings` and the principal tilt units in the
period description following `pr:teichmuller-lift-A`.
fidelity: uses the actual principal-unit subgroup of the original tilt.
Its norm-one elements give genuine integral Teichmuller coordinates.
The actual Witt constant coefficient and p-tail prove that every such
coordinate belongs to the original log convergence domain at all radii.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; the logarithmic period and its untilt
evaluation are separate consumers. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittPrincipalUnitDomain

open JoshiTeich.Prologue InitialThetaWittAllRadiusPadicScalars
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Principal := UltrametricPrincipalUnits.subgroup (InitialThetaTiltField.Carrier D w)

def integralValue : Principal D w →* InitialThetaTiltIntegers.Integers D w where
  toFun u := ⟨((u : (InitialThetaTiltField.Carrier D w)ˣ) : InitialThetaTiltField.Carrier D w),
    (LocalGeometricFontaine.mem_integerRing _ _).mpr
      (UltrametricPrincipalUnits.norm_coe (InitialThetaTiltField.Carrier D w) u).le⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem integralValue_near_one (u : Principal D w) : ‖integralValue D w u - 1‖ < 1 := by
  have hn : ‖integralValue D w u - 1‖ =
      ‖((u : (InitialThetaTiltField.Carrier D w)ˣ) : InitialThetaTiltField.Carrier D w) - 1‖ := rfl
  exact hn.trans_lt u.property

def wittUnit : Principal D w →* InitialThetaTiltFontaine.Ainf D w :=
  (WittVector.teichmuller (Arithmetic.residueChar w.1)).comp (integralValue D w)

def ainfCoordinate (u : Principal D w) : InitialThetaTiltFontaine.Ainf D w := wittUnit D w u - 1

theorem ainfCoordinate_constantCoeff (u : Principal D w) :
    (ainfCoordinate D w u).coeff 0 = integralValue D w u - 1 := by
  calc
    _ = WittVector.constantCoeff (wittUnit D w u) -
        WittVector.constantCoeff (1 : InitialThetaTiltFontaine.Ainf D w) :=
      map_sub WittVector.constantCoeff _ _
    _ = integralValue D w u - 1 := by
      rw [map_one]
      change (WittVector.teichmuller (Arithmetic.residueChar w.1) (integralValue D w u)).coeff 0 - 1 = _
      rw [WittVector.teichmuller_coeff_zero]

theorem norm_ainf_le_max (ρ : Radius) (a : InitialThetaTiltFontaine.Ainf D w) :
    ‖InitialThetaWittRhoExpansion.ainfMap D w ρ a‖ ≤ max ‖a.coeff 0‖ ρ.val.toReal := by
  obtain ⟨b, hb⟩ := InitialThetaFontaineKernel.decomposition D w a
  have hm : ‖InitialThetaWittRhoExpansion.ainfMap D w ρ
      ((Arithmetic.residueChar w.1 : InitialThetaTiltFontaine.Ainf D w) * b)‖ ≤ ρ.val.toReal := by
    rw [map_mul]
    calc
      _ ≤ ‖InitialThetaWittRhoExpansion.ainfMap D w ρ (Arithmetic.residueChar w.1)‖ *
          ‖InitialThetaWittRhoExpansion.ainfMap D w ρ b‖ := norm_mul_le _ _
      _ ≤ ‖InitialThetaWittRhoExpansion.ainfMap D w ρ (Arithmetic.residueChar w.1)‖ :=
        mul_le_of_le_one_right (norm_nonneg _) (InitialThetaWittRhoExpansion.norm_ainfMap_le_one D w ρ b)
      _ = _ := InitialThetaWittRhoExpansion.norm_ainfMap_prime D w ρ
  calc
    _ = ‖InitialThetaWittRhoExpansion.ainfMap D w ρ
          (WittVector.teichmuller (Arithmetic.residueChar w.1) (a.coeff 0)) +
        InitialThetaWittRhoExpansion.ainfMap D w ρ ((Arithmetic.residueChar w.1) * b)‖ := by
      rw [← map_add, ← hb]
    _ ≤ _ := (InitialThetaWittRhoUltrametric.norm_add_le_max D w ρ _ _).trans
      (max_le_max (InitialThetaWittTateLogarithm.norm_ainf_teichmuller D w ρ _).le hm)

def coordinate (u : Principal D w) : Carrier D w :=
  InitialThetaWittAllRadiusExpansion.ainfMap D w (ainfCoordinate D w u)

theorem coordinate_lt_one (u : Principal D w) (ρ : Radius) :
    InitialThetaWittAllRadiusCompletion.coordinateSeminorm D w ρ (coordinate D w u) < 1 := by
  change ‖InitialThetaWittRhoExpansion.ainfMap D w ρ (ainfCoordinate D w u)‖ < 1
  apply (norm_ainf_le_max D w ρ _).trans_lt
  rw [ainfCoordinate_constantCoeff]
  apply max_lt (integralValue_near_one D w u)
  simpa only [ENNReal.toReal_one] using
    (ENNReal.toReal_lt_toReal (ρ.property.2.trans ENNReal.one_lt_top).ne ENNReal.one_ne_top).mpr ρ.property.2

theorem coordinate_one : coordinate D w 1 = 0 := by
  rw [coordinate, ainfCoordinate, map_one, sub_self, map_zero]

theorem coordinate_mul (u v : Principal D w) :
    coordinate D w (u * v) = coordinate D w u + coordinate D w v + coordinate D w u * coordinate D w v := by
  simp only [coordinate, ainfCoordinate, map_mul, map_sub, map_one]
  ring

theorem coordinate_pow (u : Principal D w) (n : ℕ) :
    coordinate D w (u ^ n) = (1 + coordinate D w u) ^ n - 1 := by
  simp [coordinate, ainfCoordinate, map_pow]

end
end JoshiTeich.Act1Scene1.InitialThetaWittPrincipalUnitDomain
