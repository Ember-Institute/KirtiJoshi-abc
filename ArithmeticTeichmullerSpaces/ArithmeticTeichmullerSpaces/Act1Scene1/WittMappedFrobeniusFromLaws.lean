import ArithmeticTeichmullerSpaces.Act1Scene1.WittMappedFrobeniusData
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalizationFrobeniusFunctionNaturality

/-!
source-id: JT-SCENE1-WITT-MAPPED-FROBENIUS-FROM-LAWS
source: Joshi II `se:ff-rings`, functorial Frobenius comparison on the
integral Witt localizations; localization uniqueness.
fidelity: retains an existing norm comparison record and adds the two
supplied forward functions. Their commutation is proved from their unit,
multiplication and integral inclusion laws. The existing record supplies
the comparison function, its ring laws and its integral comparison law.
The concrete consumer must discharge every input law from its original
maps. No new equivalence, norm, or localization carrier is constructed.
The original record and both full functions are preserved by definitional
equalities. Original proofs; no reference implementation copied.
boundary: generic construction from explicit proved laws only; it supplies
no concrete source law or completion, paper B, period or BK identity.
Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.WittMappedFrobeniusFromLaws

noncomputable section

open WittMappedLocalizationComparisonData WittMappedFrobeniusData

variable {A B L T : Type*}
variable [CommRing A] [CommRing B] [CommRing L] [CommRing T]
variable {f : A → B} {i : A →+* L} {j : B →+* T} {r : A} {s : B}
variable {obsA : A → ℕ → ℝ} {obsB : B → ℕ → ℝ} {d : ℕ}

def withActions
    (C : NormData f i j r s obsA obsB d)
    [Algebra A L] [IsLocalization (Submonoid.powers r) L]
    (hi : ∀ a, i a = algebraMap A L a)
    (F : L → L) (G : T → T)
    (hF_one : F 1 = 1) (hG_one : G 1 = 1)
    (hF_mul : ∀ a b, F (a * b) = F a * F b)
    (hG_mul : ∀ a b, G (a * b) = G a * G b)
    (φ : A → A) (ψ : B → B)
    (hF : ∀ a, F (i a) = i (φ a))
    (hG : ∀ b, G (j b) = j (ψ b))
    (he : ∀ a, f (φ a) = ψ (f a)) :
    FrobeniusNormData f i j r s obsA obsB d where
  toNormData := C
  sourceFrobenius := F
  targetFrobenius := G
  on_frobenius :=
    LocalizationFrobeniusFunctionNaturality.commutes
      (Submonoid.powers r) i j hi C.locEquiv.toEquiv.toFun F G
      C.locEquiv.map_one hF_one hG_one
      C.locEquiv.map_mul hF_mul hG_mul
      f φ ψ C.on_algebraMap hF hG he

variable
    (C : NormData f i j r s obsA obsB d)
    [Algebra A L] [IsLocalization (Submonoid.powers r) L]
    (hi : ∀ a, i a = algebraMap A L a)
    (F : L → L) (G : T → T)
    (hF_one : F 1 = 1) (hG_one : G 1 = 1)
    (hF_mul : ∀ a b, F (a * b) = F a * F b)
    (hG_mul : ∀ a b, G (a * b) = G a * G b)
    (φ : A → A) (ψ : B → B)
    (hF : ∀ a, F (i a) = i (φ a))
    (hG : ∀ b, G (j b) = j (ψ b))
    (he : ∀ a, f (φ a) = ψ (f a))

theorem toNormData_eq :
    (withActions C hi F G hF_one hG_one hF_mul hG_mul φ ψ hF hG he).toNormData =
      C := rfl

theorem sourceFrobenius_eq :
    (withActions C hi F G hF_one hG_one hF_mul hG_mul φ ψ hF hG he).sourceFrobenius =
      F := rfl

theorem targetFrobenius_eq :
    (withActions C hi F G hF_one hG_one hF_mul hG_mul φ ψ hF hG he).targetFrobenius =
      G := rfl

end
end JoshiTeich.Act1Scene1.WittMappedFrobeniusFromLaws
