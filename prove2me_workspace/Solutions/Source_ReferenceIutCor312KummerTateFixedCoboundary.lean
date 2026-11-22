import Solutions.Source_ReferenceIutCor312CrystallineTateFixedAction
import Solutions.Source_ReferenceIutCor312KummerTateFrobenius
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerRationalCohomology

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open JoshiTeich.Prologue CrystallineEnvelope LocalKummer

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable [CharZero K]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "Ω₀" => Algebraic K
local notation "C" => Field K
local notation "G" => (Ω₀ ≃ₐ[K] Ω₀)
local notation "ι" => (UniformSpace.Completion.coeRingHom : Ω₀ →+* C)
local notation "𝒪" => LocalGeometricFontaine.integerRing C
local notation "B" => ACrisInvertP C p
local notation "Bₜ" => ACrisInvertTatePeriod C p ι
local notation "F" => ACrisInvertTatePeriodFrobeniusFixed C p ι

/-- The crystalline logarithm of the given root tower divided by the original
Tate period, viewed in the Frobenius-fixed ring. -/
def kummerLogOverMappedTateBasisPeriodFixed {a : K} (R : RootTower (Ω := Ω₀) p a)
    (ha : ‖(algebraMap K C a)‖ ≤ 1)
    (hu : ∃ r : 𝒪, ι (algebraMap K Ω₀ a) = (1 + (p : C) * (r : C) : C)) : ↥F :=
  ⟨kummerLogOverMappedTateBasisPeriod p R ha hu,
    (mem_ACrisInvertTatePeriodFrobeniusFixed C p ι _).2
      (frobeniusACrisInvertTatePeriod_kummerLogOverMappedTateBasisPeriod p R ha hu)⟩

/-- The image of the original rational Kummer cocycle is a coboundary for the
cyclotomically twisted action on the Frobenius-fixed ring. -/
theorem kummerLogOverMappedTateBasisPeriodFixed_coboundary
    {a : K} (R : RootTower (Ω := Ω₀) p a)
    (ha : ‖(algebraMap K C a)‖ ≤ 1)
    (hu : ∃ r : 𝒪, ι (algebraMap K Ω₀ a) = (1 + (p : C) * (r : C) : C))
    (hne : a ≠ 0) (σ : G) :
    padicMapACrisInvertTatePeriodFrobeniusFixed C p ι
        (Rational.cocycle p (R.continuousCocycleValue (Fact.out : p.Prime).pos hne) σ).down =
      galoisACrisInvertTatePeriodFrobeniusFixedTwist p σ
          (kummerLogOverMappedTateBasisPeriodFixed p R ha hu) -
        kummerLogOverMappedTateBasisPeriodFixed p R ha hu := by
  let b : ↥F := kummerLogOverMappedTateBasisPeriodFixed p R ha hu
  let g : Bₜ ≃+* Bₜ := extendGaloisACrisInvertTatePeriod p σ
  let scalar : Padic p →+* Bₜ := padicMapACrisInvertTatePeriod C p ι
  let j : B →+* Bₜ := algebraMap B Bₜ
  let χ : PadicInt p := Cyclotomic.character p σ
  let k : PadicInt p := (TateBasis.equiv (p := p) (Ω := Ω₀)).symm
    (Additive.ofMul (R.kummerCocycle (Fact.out : p.Prime).pos hne σ))
  have hscalar (x : PadicInt p) : scalar (x : Padic p) = j (padicIntMapACrisInvertP p C x) :=
    congrArg j (padicMapACrisInvertP_algebraMap p C x)
  let gFixed := galoisACrisInvertTatePeriodFrobeniusFixed p σ b
  let scalarFixed := padicMapACrisInvertTatePeriodFrobeniusFixed C p ι
  have hsmul :
      galoisACrisInvertTatePeriodFrobeniusFixedTwist p σ b =
        scalarFixed (χ : Padic p) * gFixed :=
    (galoisACrisInvertTatePeriodFrobeniusFixedTwist_apply p σ b).trans
      (smul_ACrisInvertTatePeriodFrobeniusFixed C p ι (χ : Padic p) gFixed)
  have hscalarFixed : (scalarFixed (χ : Padic p) : Bₜ) = scalar (χ : Padic p) :=
    coe_padicMapACrisInvertTatePeriodFrobeniusFixed C p ι (χ : Padic p)
  have htwist : (galoisACrisInvertTatePeriodFrobeniusFixedTwist p σ b : Bₜ) =
      scalar (χ : Padic p) * g (b : Bₜ) :=
    (congrArg (fun z : ↥F => (z : Bₜ)) hsmul).trans
      ((congrArg (fun z : Bₜ => z * (gFixed : Bₜ)) hscalarFixed).trans
        (congrArg (fun z : Bₜ => scalar (χ : Padic p) * z)
          (coe_galoisACrisInvertTatePeriodFrobeniusFixed p σ b)))
  apply Subtype.ext
  change scalar (k : Padic p) =
    (galoisACrisInvertTatePeriodFrobeniusFixedTwist p σ b : Bₜ) - (b : Bₜ)
  calc
    _ = j (padicIntMapACrisInvertP p C k) := hscalar k
    _ = j (padicIntMapACrisInvertP p C χ) * g (b : Bₜ) - (b : Bₜ) :=
      (kummerLogOverMappedTateBasisPeriod_twisted_sub p R ha hu hne σ).symm
    _ = scalar (χ : Padic p) * g (b : Bₜ) - (b : Bₜ) :=
      congrArg (fun z : Bₜ => z * g (b : Bₜ) - (b : Bₜ)) (hscalar χ).symm
    _ = _ := congrArg (fun z : Bₜ => z - (b : Bₜ)) htwist.symm

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
