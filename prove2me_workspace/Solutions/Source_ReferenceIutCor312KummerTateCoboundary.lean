import Solutions.Source_ReferenceIutCor312CrystallineTateAction
import Solutions.Source_ReferenceIutCor312KummerCrystallineCoboundary

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open JoshiTeich.Prologue CrystallineEnvelope LocalKummer

noncomputable section

private theorem twisted_sub_of_mul_period {S : Type*} [CommRing S] (g : S ≃+* S)
    (b t χ L k : S) (htUnit : IsUnit t) (hb : b * t = L) (ht : g t = χ * t)
    (hL : g L - L = k * t) : χ * g b - b = k := by
  apply htUnit.mul_right_cancel
  calc
    (χ * g b - b) * t = g b * (χ * t) - b * t := by
      rw [sub_mul, mul_comm χ (g b), mul_assoc]
    _ = g (b * t) - b * t := by rw [map_mul, ht]
    _ = k * t := by rw [hb, hL]

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "Ω₀" => Algebraic K
local notation "C" => Field K
local notation "G" => (Ω₀ ≃ₐ[K] Ω₀)
local notation "ι" => (UniformSpace.Completion.coeRingHom : Ω₀ →+* C)
local notation "𝒪" => LocalGeometricFontaine.integerRing C
local notation "A" => ACris C p
local notation "B" => ACrisInvertP C p
local notation "Bₜ" => ACrisInvertTatePeriod C p ι
local notation "t" => mappedTateBasisPeriod C p ι
local notation "i" => algebraMap A B
local notation "j" => algebraMap B Bₜ
local notation "iₜ" => (RingHom.comp (j : B →+* Bₜ) (i : A →+* B))

/-- The crystalline logarithm of the given root tower divided by the image of
the original Tate period. -/
def kummerLogOverMappedTateBasisPeriod {a : K} (R : RootTower (Ω := Ω₀) p a)
    (ha : ‖(algebraMap K C a)‖ ≤ 1)
    (hu : ∃ r : 𝒪, ι (algebraMap K Ω₀ a) = (1 + (p : C) * (r : C) : C)) : Bₜ :=
  iₜ (kummerLogOfExists C p R ι ha hu) *
    (↑((ACrisInvertTatePeriod_period_isUnit C p ι).unit⁻¹) : Bₜ)

theorem kummerLogOverMappedTateBasisPeriod_mul_period {a : K} (R : RootTower (Ω := Ω₀) p a)
    (ha : ‖(algebraMap K C a)‖ ≤ 1)
    (hu : ∃ r : 𝒪, ι (algebraMap K Ω₀ a) = (1 + (p : C) * (r : C) : C)) :
    kummerLogOverMappedTateBasisPeriod p R ha hu * j t =
      iₜ (kummerLogOfExists C p R ι ha hu) := by
  let periodUnit := (ACrisInvertTatePeriod_period_isUnit C p ι).unit
  have hperiod : (↑periodUnit : Bₜ) = j t :=
    (ACrisInvertTatePeriod_period_isUnit C p ι).unit_spec
  change iₜ (kummerLogOfExists C p R ι ha hu) * (↑periodUnit⁻¹ : Bₜ) * j t = _
  let ell : Bₜ := iₜ (kummerLogOfExists C p R ι ha hu)
  let invPeriod : Bₜ := ↑periodUnit⁻¹
  exact (congrArg (fun z : Bₜ => ell * invPeriod * z) hperiod.symm).trans
    (Units.inv_mul_cancel_right ell periodUnit)

/-- With the cyclotomic twist, the normalized logarithm gives a coboundary
for the Tate coordinate of the cocycle of the same root tower. -/
theorem kummerLogOverMappedTateBasisPeriod_twisted_sub {a : K} (R : RootTower (Ω := Ω₀) p a)
    (ha : ‖(algebraMap K C a)‖ ≤ 1)
    (hu : ∃ r : 𝒪, ι (algebraMap K Ω₀ a) = (1 + (p : C) * (r : C) : C))
    (hne : a ≠ 0) (σ : G) :
    j (padicIntMapACrisInvertP p C (Cyclotomic.character p σ : PadicInt p)) *
        extendGaloisACrisInvertTatePeriod p σ (kummerLogOverMappedTateBasisPeriod p R ha hu) -
      kummerLogOverMappedTateBasisPeriod p R ha hu =
      j (padicIntMapACrisInvertP p C ((TateBasis.equiv (p := p) (Ω := Ω₀)).symm
        (Additive.ofMul (R.kummerCocycle (Fact.out : p.Prime).pos hne σ)))) := by
  let g : Bₜ ≃+* Bₜ := extendGaloisACrisInvertTatePeriod p σ
  let b := kummerLogOverMappedTateBasisPeriod p R ha hu
  let L := kummerLogOfExists C p R ι ha hu
  let χ := j (padicIntMapACrisInvertP p C (Cyclotomic.character p σ : PadicInt p))
  let δ := R.kummerCocycle (Fact.out : p.Prime).pos hne σ
  let k := (TateBasis.equiv (p := p) (Ω := Ω₀)).symm (Additive.ofMul δ)
  have hb : b * j t = iₜ L := kummerLogOverMappedTateBasisPeriod_mul_period p R ha hu
  have ht : g (j t) = χ * j t :=
    extendGaloisACrisInvertTatePeriod_mappedTateBasisPeriod p σ
  have hδ : R.mapKummerCocycle ι hne σ = mapCyclotomicTateGroup p ι δ := by
    apply Subtype.ext
    funext n
    rfl
  have hint : extendGaloisACris p σ L - L = padicIntMapACris p C k *
      cyclotomicLog C p (mapCyclotomicTateGroup p ι (TateBasis.generator (p := p) (Ω := Ω₀))) := by
    exact (extendGaloisACris_kummerLogOfExists_sub p R ha hu hne σ).trans
      ((congrArg (cyclotomicLog C p) hδ).trans (cyclotomicLog_mapTate_eq C p ι δ))
  have hL : g (iₜ L) - iₜ L = j (padicIntMapACrisInvertP p C k) * j t := by
    change extendGaloisACrisInvertTatePeriod p σ (j (i L)) - j (i L) = _
    let f : A →+* Bₜ := iₜ
    let b₀ := extendGaloisACris p σ L
    have hg : g (f L) = f b₀ :=
      (extendGaloisACrisInvertTatePeriod_algebraMap p σ (i L)).trans
        (congrArg (j : B →+* Bₜ)
          (mapACrisInvertP_algebraMap C p (extendGaloisACris p σ) L))
    have hm := (map_sub f b₀ L).symm.trans (congrArg f hint)
    exact (congrArg (fun x : Bₜ => x - f L) hg).trans (hm.trans (map_mul f _ _))
  exact twisted_sub_of_mul_period (S := Bₜ) g b (j t) χ (iₜ L)
    (j (padicIntMapACrisInvertP p C k)) (ACrisInvertTatePeriod_period_isUnit C p ι) hb ht hL

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
