import Solutions.Source_ReferenceIutCor312RepresentativeKummerLog
import Solutions.Source_ReferenceIutConcreteLocalTheory

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField
open scoped BigOperators Pointwise

universe u v

noncomputable section

namespace LocalConstruct

private theorem incl_smul_integral_eq_of_norm_eq_one
    {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]
    (p : Nat.Primes) (c : ι → Place K) (j : ι) (w : FinitePlace K)
    (hw : c j = Place.finite w) (x : completionAt K w) (hx : ‖x‖ = 1) :
    incl p c j w hw x • integral p c = integral p c := by
  have hx0 : x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  have hinv : ‖x⁻¹‖ ≤ 1 := by simp [norm_inv, hx]
  refine Set.Subset.antisymm (smul_integral_subset p c j w hw x hx.le) ?_
  intro y hy
  let f := incl p c j w hw
  refine ⟨f (x⁻¹) * y, mul_mem_integral p c (incl_mem_integral p c j w hw _ hinv) hy, ?_⟩
  change f x * (f (x⁻¹) * y) = y
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0, map_one, one_mul]

end LocalConstruct

namespace ThetaLocalData

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}

/-- Outside the bad residue characteristics, the principal unit is of the form
`1 + p*` and its normalized ambient Kummer logarithm has norm one. -/
theorem norm_paperQRootKummerLog_eq_one_of_not_mem_badChars
    (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt)
    (hs : residueChar s ∉ TL.badChars) : ‖TL.paperQRootKummerLog s‖ = 1 := by
  rw [TL.paperQRootKummerLog_eq_paperNormalizedQRootLog,
    norm_paperNormalizedQRootLog_eq_qroot, TL.qroot_eq_one s hs, norm_one]

private abbrev concreteTheory (D : InitialThetaData AG TG) : LocalTheory.{u, u} D.Kt :=
  LocalConstruct.concreteLocalTheory (K := D.Kt)

local notation "𝓛" => concreteTheory D

/-- The product in the finite tensor of the normalized Kummer logarithms in
their respective factors. -/
def paperKummerFiniteScale (TL : ThetaLocalData D 𝓛) {ι : Type} [Fintype ι]
    (p : Nat.Primes) (c : ι → (𝓛).Fiber (.finite p)) :
    (𝓛).Tensor (.finite p) ((𝓛).tuple (.finite p) c) :=
  ∏ j : ι, (𝓛).incl p ((𝓛).tuple (.finite p) c) j ((𝓛).fiberPlace (c j))
    ((𝓛).fiberPlace_spec (c j)) (TL.paperQRootKummerLog ((𝓛).fiberPlace (c j)))

private theorem paperKummerFiniteScale_smul_integral
    (TL : ThetaLocalData D 𝓛) {ι : Type} [Fintype ι]
    (p : Nat.Primes) (c : ι → (𝓛).Fiber (.finite p))
    (hp : (p : ℕ) ∉ TL.badChars) :
    TL.paperKummerFiniteScale p c • (𝓛).integral (.finite p) ((𝓛).tuple (.finite p) c) =
      (𝓛).integral (.finite p) ((𝓛).tuple (.finite p) c) := by
  let t := (𝓛).tuple (.finite p) c
  let w (j : ι) := (𝓛).fiberPlace (c j)
  let hw (j : ι) : t j = Place.finite (w j) := (𝓛).fiberPlace_spec (c j)
  let a (j : ι) := LocalConstruct.incl p t j (w j) (hw j) (TL.paperQRootKummerLog (w j))
  change (∏ j, a j) • LocalConstruct.integral p t = LocalConstruct.integral p t
  have ha (j : ι) : a j • LocalConstruct.integral p t = LocalConstruct.integral p t := by
    have hj : residueChar (w j) ∉ TL.badChars := by
      change residueChar ((𝓛).fiberPlace (c j)) ∉ TL.badChars
      rwa [(𝓛).residueChar_fiberPlace (c j)]
    exact LocalConstruct.incl_smul_integral_eq_of_norm_eq_one p t j (w j) (hw j) _
      (TL.norm_paperQRootKummerLog_eq_one_of_not_mem_badChars (w j) hj)
  classical
  have hs (s : Finset ι) :
      (∏ j ∈ s, a j) • LocalConstruct.integral p t = LocalConstruct.integral p t := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.prod_insert hj, mul_smul, ih, ha j]
  exact hs Finset.univ

/-- Outside the bad residue characteristics, the normalized Kummer factors
give the integral packet region. -/
theorem paperKummerFiniteRegion_eq_integralRegion (TL : ThetaLocalData D 𝓛)
    (i : Fin ((D.ℓ - 1) / 2)) (p : Nat.Primes) (hp : (p : ℕ) ∉ TL.badChars) :
    let P := TL.rhsData.container.packet i (.finite p)
    P.scaledIntegral (TL.paperKummerFiniteScale p) = P.integralRegion := by
  let q := RationalPlace.finite p
  let labels := ((Procession.standard ((D.ℓ - 1) / 2)).capsule i).LabelType
  let P := (𝓛).packet labels q
  change P.scaledIntegral (TL.paperKummerFiniteScale p) = P.integralRegion
  ext x
  change (∀ c, x c ∈ TL.paperKummerFiniteScale p c • (𝓛).integral q ((𝓛).tuple q c)) ↔
    ∀ c, x c ∈ (𝓛).integral q ((𝓛).tuple q c)
  refine forall_congr' fun c => ?_
  rw [TL.paperKummerFiniteScale_smul_integral p c hp]

/-- The normalized Kummer packet region has zero log-volume away from the
bad residue characteristics. -/
theorem packetVol_paperKummerFiniteRegion_eq_zero (TL : ThetaLocalData D 𝓛)
    (i : Fin ((D.ℓ - 1) / 2)) (p : Nat.Primes) (hp : (p : ℕ) ∉ TL.badChars) :
    let R := TL.rhsData
    R.vol.packetVol i (.finite p)
      ((R.container.packet i (.finite p)).scaledIntegral (TL.paperKummerFiniteScale p)) = 0 := by
  let R := TL.rhsData
  let j : Fin R.container.proc.length := i
  let q := RationalPlace.finite p
  change R.vol.packetVol j q
    ((R.container.packet j q).scaledIntegral (TL.paperKummerFiniteScale p)) = 0
  have h : (R.container.packet j q).scaledIntegral (TL.paperKummerFiniteScale p) =
      (R.container.packet j q).integralRegion :=
    TL.paperKummerFiniteRegion_eq_integralRegion i p hp
  exact (congrArg (R.vol.packetVol j q) h).trans (R.vol.packetVol_integral j q)

end ThetaLocalData

end

end AbcAdaptation.Reference.Iut
