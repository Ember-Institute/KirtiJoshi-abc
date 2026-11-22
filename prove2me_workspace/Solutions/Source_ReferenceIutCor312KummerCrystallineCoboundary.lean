import Solutions.Source_ReferenceIutCor312CrystallineGalois
import Solutions.Source_ReferenceIutCor312CrystallineLogAdd
import Solutions.Source_ReferenceIutCor312CrystallineLogNaturality
import Solutions.Source_ReferenceIutCor312KummerFontaineGalois

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open JoshiTeich.Prologue CrystallineEnvelope

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "Ω₀" => Algebraic K
local notation "C" => Field K
local notation "ι" => (UniformSpace.Completion.coeRingHom : Ω₀ →+* C)
local notation "θ" =>
  (Perfectoid.thetaMap (O := LocalGeometricFontaine.integerRing C) (p := p))

/-- The Galois difference of the original Kummer logarithm is the crystalline
logarithm of the original Kummer cocycle value in the same completion. -/
theorem extendGaloisACris_kummerLogOfExists_sub
    {a : K} (R : LocalKummer.RootTower (Ω := Algebraic K) p a)
    (ha : ‖(algebraMap K C a)‖ ≤ 1)
    (hu : ∃ r : LocalGeometricFontaine.integerRing C,
      ι (algebraMap K Ω₀ a) = 1 + (p : C) * (r : C))
    (hne : a ≠ 0) (σ : Ω₀ ≃ₐ[K] Ω₀) :
    extendGaloisACris p σ (kummerLogOfExists C p R ι ha hu) -
      kummerLogOfExists C p R ι ha hu =
        cyclotomicLog C p (R.mapKummerCocycle ι hne σ) := by
  let ε := R.mapKummerCocycle ι hne σ
  let x := teichmullerSubOne C p (CyclotomicTateTilt.toPreTilt C p ε)
  let y := teichmullerSubOne C p (R.toGeometricPreTilt ι ha)
  let f : Ainf C p →+* Ainf C p := (extendGaloisFontaine p σ).toRingHom
  have hle : RingHom.ker θ ≤ kerSupPrime C p := le_sup_left
  have hx : x ∈ kerSupPrime C p :=
    hle (LocalKummer.RootTower.cyclotomic_teichmuller_sub_one_mem_theta_ker ε)
  have hy : y ∈ kerSupPrime C p :=
    kummerTeichmullerSubOne_mem_kerSupPrime C p R ι ha hu
  have hfy : f y ∈ kerSupPrime C p := extendGaloisFontaine_mem_kerSupPrime p σ hy
  have hmap :
      extendGaloisACris p σ (logOfMemKerSupPrime C p y hy) =
        logOfMemKerSupPrime C p (f y) hfy := by
    unfold extendGaloisACris extendGaloisA0
    exact mapACris_logOfMemKerSupPrime C p f
      (fun _ h => extendGaloisFontaine_mem_kerSupPrime p σ (hle h)) hy hfy rfl
  have one_add (u : GeometricTiltField.Source C p) :
      1 + teichmullerSubOne C p u = WittVector.teichmuller p u := by
    rw [teichmullerSubOne, add_comm (1 : Ainf C p), sub_add_cancel]
  have hx_add : 1 + x = WittVector.teichmuller p (CyclotomicTateTilt.toPreTilt C p ε) :=
    one_add _
  have hy_add : 1 + y = WittVector.teichmuller p (R.toGeometricPreTilt ι ha) := one_add _
  have hprod : 1 + f y = (1 + x) * (1 + y) := by
    calc
      1 + f y = f (1 + y) := by rw [map_add, map_one]
      _ = _ := by
        rw [hx_add, hy_add]
        exact R.extendGaloisFontaine_teichmuller_toGeometricPreTilt ha hne σ
  change extendGaloisACris p σ (logOfMemKerSupPrime C p y hy) -
    logOfMemKerSupPrime C p y hy = logOfMemKerSupPrime C p x hx
  exact sub_eq_iff_eq_add.mpr
    (hmap.trans (logOfMemKerSupPrime_mul C p x y (f y) hx hy hfy hprod))

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
