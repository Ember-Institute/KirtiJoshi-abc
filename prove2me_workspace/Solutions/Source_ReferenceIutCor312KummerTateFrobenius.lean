import Solutions.Source_ReferenceIutCor312CrystallineTateFrobenius
import Solutions.Source_ReferenceIutCor312KummerTateCoboundary

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open JoshiTeich.Prologue CrystallineEnvelope LocalKummer

noncomputable section

private theorem fixed_of_mul_eigen {S : Type*} [CommRing S]
    (f : S →+* S) (c t b L : S) (hc : IsUnit c) (htUnit : IsUnit t)
    (hb : b * t = L) (ht : f t = c * t) (hL : f L = c * L) :
    f b = b := by
  apply (hc.mul htUnit).mul_right_cancel
  calc
    f b * (c * t) = f (b * t) :=
      (congrArg (fun z => f b * z) ht.symm).trans (map_mul f b t).symm
    _ = f L := congrArg f hb
    _ = c * L := hL
    _ = c * (b * t) := congrArg (fun z => c * z) hb.symm
    _ = b * (c * t) := mul_left_comm c b t

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "Ω₀" => Algebraic K
local notation "C" => Field K
local notation "ι" => (UniformSpace.Completion.coeRingHom : Ω₀ →+* C)
local notation "𝒪" => LocalGeometricFontaine.integerRing C
local notation "A" => ACris C p
local notation "B" => ACrisInvertP C p
local notation "Bₜ" => ACrisInvertTatePeriod C p ι
local notation "t" => mappedTateBasisPeriod C p ι
local notation "i" => algebraMap A B
local notation "j" => algebraMap B Bₜ

/-- The logarithm of the given Kummer root tower divided by the original Tate
period is fixed by crystalline Frobenius. -/
theorem frobeniusACrisInvertTatePeriod_kummerLogOverMappedTateBasisPeriod
    {a : K} (R : RootTower (Ω := Ω₀) p a) (ha : ‖(algebraMap K C a)‖ ≤ 1)
    (hu : ∃ r : 𝒪, ι (algebraMap K Ω₀ a) = (1 + (p : C) * (r : C) : C)) :
    frobeniusACrisInvertTatePeriod C p ι (kummerLogOverMappedTateBasisPeriod p R ha hu) =
      kummerLogOverMappedTateBasisPeriod p R ha hu := by
  let φ := frobeniusACrisInvertTatePeriod C p ι
  let b := kummerLogOverMappedTateBasisPeriod p R ha hu
  let L := kummerLogOfExists C p R ι ha hu
  let T : Bₜ := j t
  let F : Bₜ := j (i L)
  have hb : b * T = F :=
    kummerLogOverMappedTateBasisPeriod_mul_period p R ha hu
  have hT : φ T = (p : Bₜ) * T :=
    frobeniusACrisInvertTatePeriod_mappedTateBasisPeriod C p ι
  have hL : φ F = (p : Bₜ) * F :=
    frobeniusACrisInvertTatePeriod_eigen C p ι L
      (frobeniusACris_kummerLogOfExists_eq_prime_mul C p R ι ha hu)
  exact fixed_of_mul_eigen (S := Bₜ) φ (p : Bₜ) T b F
    (ACrisInvertTatePeriod_prime_isUnit C p ι)
    (ACrisInvertTatePeriod_period_isUnit C p ι) hb hT hL

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
