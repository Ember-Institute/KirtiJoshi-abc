import Solutions.Source_ReferenceIutCor312CrystallineGalois
import Solutions.Source_ReferenceIutCor312CrystallineFrobenius
import Solutions.Source_ReferenceIutCor312CrystallineInvertP
import Solutions.Source_ReferenceIutCor312CrystallineA0HomExt

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open JoshiTeich.Prologue CrystallineEnvelope

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]

local notation "Ω" => Algebraic K
local notation "C" => Field K
local notation "𝒪" => LocalGeometricFontaine.integerRing C
local notation "W" => Ainf C p
local notation "D" => A0 C p
local notation "𝔭₀" => (Ideal.span {(p : D)} : Ideal D)
local notation "A" => ACris C p
local notation "B" => ACrisInvertP C p

private theorem extendGaloisIntegers_one_apply (x : 𝒪) :
    extendGaloisIntegers (1 : Ω ≃ₐ[K] Ω) x = x := by
  apply Subtype.ext
  change galoisCompletion (1 : Ω ≃ₐ[K] Ω) (x : C) = (x : C)
  rw [map_one]
  rfl

private theorem extendGaloisIntegers_mul_apply (σ τ : Ω ≃ₐ[K] Ω) (x : 𝒪) :
    extendGaloisIntegers (σ * τ) x = extendGaloisIntegers σ (extendGaloisIntegers τ x) := by
  apply Subtype.ext
  change galoisCompletion (σ * τ) (x : C) = galoisCompletion σ (galoisCompletion τ (x : C))
  rw [map_mul]
  rfl

omit [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)] in
private theorem extendGaloisModP_one_apply (x : ModP 𝒪 p) :
    extendGaloisModP p (1 : Ω ≃ₐ[K] Ω) x = x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [extendGaloisModP_mk, extendGaloisIntegers_one_apply]

omit [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)] in
private theorem extendGaloisModP_mul_apply (σ τ : Ω ≃ₐ[K] Ω) (x : ModP 𝒪 p) :
    extendGaloisModP p (σ * τ) x = extendGaloisModP p σ (extendGaloisModP p τ x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [extendGaloisModP_mk, extendGaloisModP_mk, extendGaloisModP_mk,
    extendGaloisIntegers_mul_apply]

private theorem extendGaloisPreTilt_one_apply (x : GeometricTiltField.Source C p) :
    extendGaloisPreTilt p (1 : Ω ≃ₐ[K] Ω) x = x := by
  apply Perfection.ext
  intro n
  rw [coeff_extendGaloisPreTilt, extendGaloisModP_one_apply]

private theorem extendGaloisPreTilt_mul_apply (σ τ : Ω ≃ₐ[K] Ω)
    (x : GeometricTiltField.Source C p) :
    extendGaloisPreTilt p (σ * τ) x = extendGaloisPreTilt p σ (extendGaloisPreTilt p τ x) := by
  apply Perfection.ext
  intro n
  rw [coeff_extendGaloisPreTilt, coeff_extendGaloisPreTilt, coeff_extendGaloisPreTilt,
    extendGaloisModP_mul_apply]

private theorem extendGaloisFontaine_one_apply (x : W) :
    extendGaloisFontaine p (1 : Ω ≃ₐ[K] Ω) x = x := by
  apply WittVector.ext
  intro n
  rw [coeff_extendGaloisFontaine, extendGaloisPreTilt_one_apply]

private theorem extendGaloisFontaine_mul_apply (σ τ : Ω ≃ₐ[K] Ω) (x : W) :
    extendGaloisFontaine p (σ * τ) x = extendGaloisFontaine p σ (extendGaloisFontaine p τ x) := by
  apply WittVector.ext
  intro n
  rw [coeff_extendGaloisFontaine, coeff_extendGaloisFontaine, coeff_extendGaloisFontaine,
    extendGaloisPreTilt_mul_apply]

private theorem extendGaloisFontaine_frobenius (σ : Ω ≃ₐ[K] Ω) (x : W) :
    extendGaloisFontaine p σ (WittVector.frobenius x) =
      WittVector.frobenius (extendGaloisFontaine p σ x) := by
  apply WittVector.ext
  intro n
  rw [coeff_extendGaloisFontaine, WittVector.coeff_frobenius_charP,
    WittVector.coeff_frobenius_charP, coeff_extendGaloisFontaine, map_pow]

private theorem extendGaloisA0_one_apply (x : D) :
    extendGaloisA0 p (1 : Ω ≃ₐ[K] Ω) x = x := by
  have h : extendGaloisA0 p (1 : Ω ≃ₐ[K] Ω) = RingHom.id D := by
    apply ringHom_ext_of_Ainf p
    intro y
    simp only [extendGaloisA0_algebraMap, extendGaloisFontaine_one_apply, RingHom.id_apply]
  exact RingHom.congr_fun h x

private theorem extendGaloisA0_mul_apply (σ τ : Ω ≃ₐ[K] Ω) (x : D) :
    extendGaloisA0 p (σ * τ) x = extendGaloisA0 p σ (extendGaloisA0 p τ x) := by
  have h : extendGaloisA0 p (σ * τ) = (extendGaloisA0 p σ).comp (extendGaloisA0 p τ) := by
    apply ringHom_ext_of_Ainf p
    intro y
    simp only [RingHom.comp_apply, extendGaloisA0_algebraMap, extendGaloisFontaine_mul_apply]
  exact RingHom.congr_fun h x

private theorem extendGaloisA0_frobenius (σ : Ω ≃ₐ[K] Ω) (x : D) :
    extendGaloisA0 p σ (frobeniusA0 C p x) = frobeniusA0 C p (extendGaloisA0 p σ x) := by
  have h : (extendGaloisA0 p σ).comp (frobeniusA0 C p) =
      (frobeniusA0 C p).comp (extendGaloisA0 p σ) := by
    apply ringHom_ext_of_Ainf p
    intro y
    simp only [RingHom.comp_apply, extendGaloisA0_algebraMap]
    unfold frobeniusA0
    simp only [mapA0_algebraMap, extendGaloisA0_algebraMap, extendGaloisFontaine_frobenius]
  exact RingHom.congr_fun h x

theorem extendGaloisACris_one_apply (z : A) :
    extendGaloisACris p (1 : Ω ≃ₐ[K] Ω) z = z := by
  apply AdicCompletion.ext_evalₐ (I := 𝔭₀)
  intro n
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ 𝔭₀ n z)
  calc
    _ = Ideal.Quotient.mk (𝔭₀ ^ n) (extendGaloisA0 p 1 a) :=
      eval_mapACris_of_eq C p (extendGaloisA0 p 1) n z a ha.symm
    _ = _ := (congrArg (Ideal.Quotient.mk (𝔭₀ ^ n)) (extendGaloisA0_one_apply p a)).trans ha

private theorem eval_mapACris_twice_of_eq (f g : D →+* D) (n : ℕ) (z : A) (a : D)
    (ha : AdicCompletion.evalₐ 𝔭₀ n z = Ideal.Quotient.mk (𝔭₀ ^ n) a) :
    AdicCompletion.evalₐ 𝔭₀ n (mapACris C p f (mapACris C p g z)) =
      Ideal.Quotient.mk (𝔭₀ ^ n) (f (g a)) :=
  eval_mapACris_of_eq C p f n _ _ (eval_mapACris_of_eq C p g n z a ha)

theorem extendGaloisACris_mul_apply (σ τ : Ω ≃ₐ[K] Ω) (z : A) :
    extendGaloisACris p (σ * τ) z = extendGaloisACris p σ (extendGaloisACris p τ z) := by
  apply AdicCompletion.ext_evalₐ (I := 𝔭₀)
  intro n
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ 𝔭₀ n z)
  calc
    _ = Ideal.Quotient.mk (𝔭₀ ^ n) (extendGaloisA0 p (σ * τ) a) :=
      eval_mapACris_of_eq C p (extendGaloisA0 p (σ * τ)) n z a ha.symm
    _ = Ideal.Quotient.mk (𝔭₀ ^ n) (extendGaloisA0 p σ (extendGaloisA0 p τ a)) :=
      congrArg (Ideal.Quotient.mk (𝔭₀ ^ n)) (extendGaloisA0_mul_apply p σ τ a)
    _ = _ := (eval_mapACris_twice_of_eq p (extendGaloisA0 p σ) (extendGaloisA0 p τ) n z a ha.symm).symm

theorem extendGaloisACris_frobenius (σ : Ω ≃ₐ[K] Ω) (z : A) :
    extendGaloisACris p σ (frobeniusACris C p z) = frobeniusACris C p (extendGaloisACris p σ z) := by
  apply AdicCompletion.ext_evalₐ (I := 𝔭₀)
  intro n
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ 𝔭₀ n z)
  have hs := eval_mapACris_twice_of_eq p (extendGaloisA0 p σ) (frobeniusA0 C p) n z a ha.symm
  have ht := eval_mapACris_twice_of_eq p (frobeniusA0 C p) (extendGaloisA0 p σ) n z a ha.symm
  exact (hs.trans (congrArg (Ideal.Quotient.mk (𝔭₀ ^ n)) (extendGaloisA0_frobenius p σ a))).trans ht.symm

theorem extendGaloisACrisInvertP_one_apply (z : B) :
    mapACrisInvertP C p (extendGaloisACris p (1 : Ω ≃ₐ[K] Ω)) z = z := by
  have h : mapACrisInvertP C p (extendGaloisACris p (1 : Ω ≃ₐ[K] Ω)) = RingHom.id B := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (p : A)) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, RingHom.id_apply, mapACrisInvertP_algebraMap,
      extendGaloisACris_one_apply]
  exact RingHom.congr_fun h z

theorem extendGaloisACrisInvertP_mul_apply (σ τ : Ω ≃ₐ[K] Ω) (z : B) :
    mapACrisInvertP C p (extendGaloisACris p (σ * τ)) z =
      mapACrisInvertP C p (extendGaloisACris p σ)
        (mapACrisInvertP C p (extendGaloisACris p τ) z) := by
  have h : mapACrisInvertP C p (extendGaloisACris p (σ * τ)) =
      (mapACrisInvertP C p (extendGaloisACris p σ)).comp
        (mapACrisInvertP C p (extendGaloisACris p τ)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (p : A)) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, mapACrisInvertP_algebraMap, extendGaloisACris_mul_apply]
  exact RingHom.congr_fun h z

theorem extendGaloisACrisInvertP_frobenius (σ : Ω ≃ₐ[K] Ω) (z : B) :
    mapACrisInvertP C p (extendGaloisACris p σ) (mapACrisInvertP C p (frobeniusACris C p) z) =
      mapACrisInvertP C p (frobeniusACris C p) (mapACrisInvertP C p (extendGaloisACris p σ) z) := by
  have h : (mapACrisInvertP C p (extendGaloisACris p σ)).comp (mapACrisInvertP C p (frobeniusACris C p)) =
      (mapACrisInvertP C p (frobeniusACris C p)).comp (mapACrisInvertP C p (extendGaloisACris p σ)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (p : A)) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, mapACrisInvertP_algebraMap, extendGaloisACris_frobenius]
  exact RingHom.congr_fun h z

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
