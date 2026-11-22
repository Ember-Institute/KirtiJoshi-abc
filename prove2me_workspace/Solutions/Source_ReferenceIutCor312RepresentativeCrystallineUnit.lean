import Solutions.Source_ReferenceIutCor312RepresentativeCrystallineCompletion
import Solutions.Source_ReferenceIutCor312RepresentativeKummerLog

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1 JoshiTeich.Prologue.Arithmetic

universe u v

noncomputable section

private theorem rationalKummerHom_toAdd_eq_classOfCocycle {K Ω : Type*} [Field K] [Field Ω]
    [Algebra K Ω] [Algebra.IsIntegral K Ω] [CharZero Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime] (a : Kˣ) :
    (LocalKummer.Rational.kummerHom (Ω := Ω) p a).toAdd =
      LocalKummer.Rational.classOfCocycle (K := K) (Ω := Ω) p
        ((LocalKummer.rootTower (Ω := Ω) p (Fact.out : p.Prime).pos (a : K)).continuousCocycleValue
          (Fact.out : p.Prime).pos a.ne_zero) :=
  LocalKummer.Rational.toH1_class (K := K) (Ω := Ω) p
    ((LocalKummer.rootTower (K := K) (Ω := Ω) p (Fact.out : p.Prime).pos (a : K)).continuousCocycleValue
      (Fact.out : p.Prime).pos a.ne_zero)

local instance representativeCrystallineUnitPrime {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) : Fact (residueChar s).Prime :=
  LocalCompletion.selectedPrime s

local instance representativeCrystallineCharZero {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) : CharZero (LocalCompletion.completionAt K s) :=
  LocalCompletion.completionCharZero s

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}
variable (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt)

local notation "pₛ" => residueChar s
local notation "E" => LocalCompletion.completionAt D.Kt s
local notation "Ωₛ" => AlgebraicClosure E
local notation "Cₛ" => PadicComplex pₛ
local notation "𝒪" => LocalGeometricFontaine.integerRing Cₛ

/-- The chosen root tower used by the rational Kummer class of the paper principal unit. -/
def paperQRootKummerRootTower :
    LocalKummer.RootTower (K := E) (Ω := Ωₛ) pₛ ((TL.paperQRootPrincipalUnit s).1 : E) :=
  LocalKummer.rootTower (K := E) (Ω := Ωₛ) pₛ (residueChar_prime s).pos
    ((TL.paperQRootPrincipalUnit s).1 : E)

theorem paperQRootKummerClass_eq_rootTower :
    TL.paperQRootKummerClass s = LocalKummer.Rational.classOfCocycle (K := E) (Ω := Ωₛ) pₛ
      ((TL.paperQRootKummerRootTower s).continuousCocycleValue
        (residueChar_prime s).pos (TL.paperQRootPrincipalUnit s).1.ne_zero) :=
  rationalKummerHom_toAdd_eq_classOfCocycle (K := E) (Ω := Ωₛ) pₛ
    (TL.paperQRootPrincipalUnit s).1

private theorem paperQRootPrincipalUnit_coe :
    ((TL.paperQRootPrincipalUnit s).1 : E) =
      1 + (LocalPadicLog.paperScale pₛ : E) * TL.qroot s := rfl

private theorem paperQRootPrincipalUnit_image :
    algebraicClosureInPadicComplex s
      (algebraMap E Ωₛ ((TL.paperQRootPrincipalUnit s).1 : E)) =
      LocalPadicLog.paperPrincipalUnit pₛ (TL.qrootInPadicComplex s) := by
  let j : E →+* Cₛ := (algebraicClosureInPadicComplex s).comp (algebraMap E Ωₛ)
  have hq : j (TL.qroot s) = TL.qrootInPadicComplex s :=
    algebraicClosureInPadicComplex_algebraMap s (TL.qroot s)
  change j ((TL.paperQRootPrincipalUnit s).1 : E) = _
  rw [paperQRootPrincipalUnit_coe, map_add, map_one, map_mul, map_natCast, hq]
  rfl

private theorem paperQRoot_norm_le_one : ‖TL.qrootInPadicComplex s‖ ≤ 1 := by
  change ‖completionInPadicComplex s (TL.qroot s)‖ ≤ 1
  apply (pow_le_one_iff_of_nonneg (norm_nonneg _) (localDeg_pos s).ne').mp
  exact (completionInPadicComplex_norm_pow s (TL.qroot s)).trans_le
    (LocalConstruct.norm_le_one_of_ordp_nonneg (TL.ordp_qroot_nonneg s))

/-- The same principal unit is integral in standard `ℂ_p` and is congruent to one modulo `p`. -/
theorem paperQRootPrincipalUnit_crystalline_inputs :
    let a := algebraicClosureInPadicComplex s
      (algebraMap E Ωₛ ((TL.paperQRootPrincipalUnit s).1 : E))
    ‖a‖ ≤ 1 ∧ ∃ r : 𝒪, a = 1 + (pₛ : Cₛ) * (r : Cₛ) :=
  (paperQRootPrincipalUnit_image TL s).symm ▸
    paperPrincipalUnit_integral (C := Cₛ) pₛ (TL.qrootInPadicComplex s)
      (paperQRoot_norm_le_one TL s)

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
