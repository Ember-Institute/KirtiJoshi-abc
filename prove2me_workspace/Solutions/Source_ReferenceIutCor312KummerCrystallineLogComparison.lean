import Solutions.Source_ReferenceIutCor312CrystallineLogComparison
import Solutions.Source_ReferenceIutCor312RootTowerPreTiltComparison
import Solutions.Source_ReferenceIutCor312KummerCocyclePreTiltComparison

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue GeometricTiltComparison

noncomputable section

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
variable {C C' : Type*} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable [NormedField C'] [IsUltrametricDist C'] [CompleteSpace C']
variable (p : ℕ) [Fact p.Prime]
variable [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable [Fact (0 < ‖(p : C')‖ ∧ ‖(p : C')‖ < 1)]
variable (e : C ≃+* C') (d : ℕ) (hd : 0 < d) (hnorm : ∀ x : C, ‖e x‖ ^ d = ‖x‖)

local notation "τ" => preTiltEquiv e d hd hnorm p

private theorem mapEquiv_teichmullerSubOne_of_eq
    {x : GeometricTiltField.Source C p} {y : GeometricTiltField.Source C' p} (hxy : τ x = y) :
    WittRingEquiv.mapEquiv p τ (teichmullerSubOne C p x) = teichmullerSubOne C' p y := by
  simp only [teichmullerSubOne, map_sub, map_one, WittRingEquiv.mapEquiv_teichmuller, hxy]

variable {a : K} (R : LocalKummer.RootTower (Ω := Ω) p a)
variable (j : Ω →+* C) (j' : Ω →+* C') (hmap : ∀ z : Ω, e (j z) = j' z)

include hmap

/-- The norm-power comparison carries the crystalline Kummer logarithm of the
original tower to its logarithm under the other embedding. -/
theorem equivACris_kummerLogOfExists
    [IsAlgClosed C] [IsAlgClosed C']
    (ha : ‖j (algebraMap K Ω a)‖ ≤ 1) (ha' : ‖j' (algebraMap K Ω a)‖ ≤ 1)
    (hu : ∃ r : LocalGeometricFontaine.integerRing C, j (algebraMap K Ω a) = 1 + (p : C) * (r : C))
    (hu' : ∃ r : LocalGeometricFontaine.integerRing C',
      j' (algebraMap K Ω a) = 1 + (p : C') * (r : C')) :
    equivACris p e d hd hnorm (kummerLogOfExists C p R j ha hu) =
      kummerLogOfExists C' p R j' ha' hu' :=
  equivACris_logOfMemKerSupPrime p e d hd hnorm
    (kummerTeichmullerSubOne_mem_kerSupPrime C p R j ha hu)
    (kummerTeichmullerSubOne_mem_kerSupPrime C' p R j' ha' hu')
    (mapEquiv_teichmullerSubOne_of_eq p e d hd hnorm
      (LocalKummer.RootTower.preTiltEquiv_toGeometricPreTilt e d hd hnorm R j j' hmap ha ha'))

/-- The norm-power comparison carries the logarithm of the original Kummer
cocycle to the logarithm of the same value under the other embedding. -/
theorem equivACris_mapKummerCocycle_log (hne : a ≠ 0) (σ : Ω ≃ₐ[K] Ω) :
    equivACris p e d hd hnorm (cyclotomicLog C p (R.mapKummerCocycle j hne σ)) =
      cyclotomicLog C' p (R.mapKummerCocycle j' hne σ) := by
  let ε := R.mapKummerCocycle j hne σ
  let ε' := R.mapKummerCocycle j' hne σ
  have hx : teichmullerSubOne C p (CyclotomicTateTilt.toPreTilt C p ε) ∈ kerSupPrime C p :=
    Ideal.mem_sup_left (LocalKummer.RootTower.cyclotomic_teichmuller_sub_one_mem_theta_ker ε)
  have hy : teichmullerSubOne C' p (CyclotomicTateTilt.toPreTilt C' p ε') ∈ kerSupPrime C' p :=
    Ideal.mem_sup_left (LocalKummer.RootTower.cyclotomic_teichmuller_sub_one_mem_theta_ker ε')
  exact equivACris_logOfMemKerSupPrime p e d hd hnorm hx hy
    (mapEquiv_teichmullerSubOne_of_eq p e d hd hnorm
      (LocalKummer.RootTower.preTiltEquiv_toPreTilt_mapKummerCocycle e d hd hnorm R j j' hmap hne σ))

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
