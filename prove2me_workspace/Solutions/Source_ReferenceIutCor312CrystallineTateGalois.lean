import Solutions.Source_ReferenceIutCor312CrystallineGalois
import Solutions.Source_ReferenceIutCor312CrystallineLogNaturality
import Solutions.Source_ReferenceIutCor312MappedTatePeriod
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerCyclotomicCharacter

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open JoshiTeich.Prologue CrystallineEnvelope LocalKummer

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "Ω₀" => Algebraic K
local notation "C" => Field K
local notation "ι" => (UniformSpace.Completion.coeRingHom : Ω₀ →+* C)
local notation "𝒪" => LocalGeometricFontaine.integerRing C
local notation "q" => Ideal.Quotient.mk (Ideal.span {(p : 𝒪)})

private theorem extendGaloisPreTilt_mapCyclotomicTateGroup
    (σ : Ω₀ ≃ₐ[K] Ω₀) (δ : cyclotomicTateGroup p Ω₀) :
    extendGaloisPreTilt p σ (CyclotomicTateTilt.toPreTilt C p (mapCyclotomicTateGroup p ι δ)) =
      CyclotomicTateTilt.toPreTilt C p (mapCyclotomicTateGroup p ι (tateAction p σ δ)) := by
  apply Perfection.ext
  intro n
  rw [coeff_extendGaloisPreTilt]
  change extendGaloisModP p σ (q (CyclotomicTateTilt.coordinate C p
    (mapCyclotomicTateGroup p ι δ) n)) = q (CyclotomicTateTilt.coordinate C p
    (mapCyclotomicTateGroup p ι (tateAction p σ δ)) n)
  rw [extendGaloisModP_mk]
  apply congrArg q
  apply Subtype.ext
  exact (extendGaloisIntegers_coe σ _).trans (extendGalois_coe σ (δ.1 n : Ω₀))

/-- The crystalline Galois action on the logarithm comes from the original
Galois action on the cyclotomic tower. -/
theorem extendGaloisACris_cyclotomicLog_mapTate
    (σ : Ω₀ ≃ₐ[K] Ω₀) (δ : cyclotomicTateGroup p Ω₀) :
    extendGaloisACris p σ (cyclotomicLog C p (mapCyclotomicTateGroup p ι δ)) =
      cyclotomicLog C p (mapCyclotomicTateGroup p ι (tateAction p σ δ)) := by
  unfold extendGaloisACris extendGaloisA0 cyclotomicLog
  apply mapACris_logOfMemKerSupPrime
  rw [map_sub, map_one]
  change extendGaloisFontaine p σ
    (WittVector.teichmuller p (CyclotomicTateTilt.toPreTilt C p (mapCyclotomicTateGroup p ι δ))) - 1 = _
  rw [extendGaloisFontaine_teichmuller, extendGaloisPreTilt_mapCyclotomicTateGroup]

variable [CharZero K]

local notation "ε" => (TateBasis.generator (p := p) (Ω := Ω₀))
local notation "t" => cyclotomicLog C p (mapCyclotomicTateGroup p ι ε)

/-- The logarithm of the original Tate basis transforms by the cyclotomic
character in the integral crystalline ring. -/
theorem extendGaloisACris_mappedTateBasisLog (σ : Ω₀ ≃ₐ[K] Ω₀) :
    extendGaloisACris p σ t = padicIntMapACris p C (Cyclotomic.character p σ : PadicInt p) * t := by
  have hχ : (Cyclotomic.character p σ : PadicInt p) =
      (TateBasis.equiv (p := p) (Ω := Ω₀)).symm (Additive.ofMul (tateAction p σ ε)) := by
    rw [Cyclotomic.character_val, Cyclotomic.coefficient, TateBasis.equiv_apply, one_smul]
    rfl
  rw [extendGaloisACris_cyclotomicLog_mapTate,
    cyclotomicLog_mapTate_eq C p ι (tateAction p σ ε), hχ]

/-- The Galois formula for the original Tate period in `A_cris[1/p]`. -/
theorem extendGaloisACrisInvertP_mappedTateBasisPeriod (σ : Ω₀ ≃ₐ[K] Ω₀) :
    mapACrisInvertP C p (extendGaloisACris p σ) (mappedTateBasisPeriod C p ι) =
      padicIntMapACrisInvertP p C (Cyclotomic.character p σ : PadicInt p) *
        mappedTateBasisPeriod C p ι := by
  let i : ACris C p →+* ACrisInvertP C p := algebraMap _ _
  let f : ACris C p →+* ACris C p := extendGaloisACris p σ
  let c : ACris C p := padicIntMapACris p C (Cyclotomic.character p σ : PadicInt p)
  change mapACrisInvertP C p f (i t) = i c * i t
  exact (mapACrisInvertP_algebraMap C p f t).trans
    ((congrArg i (extendGaloisACris_mappedTateBasisLog p σ)).trans (map_mul i c t))

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
