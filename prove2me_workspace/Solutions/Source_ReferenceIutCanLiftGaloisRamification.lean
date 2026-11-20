/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors

Original repository https://github.com/lana-agents/orbicurve-cores
Original revision 61616dcd77fbe45c083a8ebfa7cc80728f86e841
Original path OrbicurveCores/U2/GaloisClosure.lean
The faithful action and tame inertia comparison come from Pi1/Orbicurve/Pullback.lean
at revision ca7def953193f861a462aa0831eec8f0a31ff69f (Apache-2.0).
-/
import Solutions.Source_ReferenceIutCanLiftGaloisCore
import Solutions.Source_ReferenceIutCanLiftTameInertia
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationInertia
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.Ideal.GoingUp

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open IntermediateField
open scoped Pointwise

universe u

private theorem subgroup_eq_of_card_eq {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (H K : Subgroup G) (h : Nat.card H = Nat.card K) : H = K := by
  letI : CommGroup G := IsCyclic.commGroup
  have eq_ker (J : Subgroup G) : J = (powMonoidHom (Nat.card J) : G →* G).ker := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      change x ^ Nat.card J = 1
      exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : J)))
    · rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right J.card_subgroup_dvd_card]
  rw [eq_ker H, eq_ker K, h]

private theorem card_inertia_inf_map_conj {B G : Type*} [CommRing B] [Group G]
    [MulSemiringAction G B] (σ : G) (H : Subgroup G) (P : Ideal B) :
    Nat.card (((σ • P).inertia G) ⊓ H.map (MulAut.conj σ).toMonoidHom : Subgroup G) =
      Nat.card ((P.inertia G) ⊓ H : Subgroup G) := by
  let c := (MulAut.conj σ).toMonoidHom
  have hmap : ((P.inertia G) ⊓ H).map c = (σ • P).inertia G ⊓ H.map c := by
    ext τ
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, c]
    constructor
    · rintro ⟨ρ, ⟨hρ, hρH⟩, rfl⟩
      refine ⟨?_, ρ, hρH, rfl⟩
      intro x
      have e : (σ * ρ * σ⁻¹) • x - x = σ • (ρ • (σ⁻¹ • x) - σ⁻¹ • x) := by
        rw [smul_sub, mul_smul, mul_smul, smul_inv_smul]
      rw [e]
      exact Ideal.smul_mem_pointwise_smul σ _ _ (hρ (σ⁻¹ • x))
    · rintro ⟨hτ, ρ, hρH, rfl⟩
      refine ⟨ρ, ⟨?_, hρH⟩, rfl⟩
      intro x
      have hx : (σ * ρ * σ⁻¹) • (σ • x) - σ • x ∈ σ • P := hτ (σ • x)
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hx
      have e : ρ • x - x = σ⁻¹ • ((σ * ρ * σ⁻¹) • (σ • x) - σ • x) := by
        simp only [smul_sub, mul_smul, inv_smul_smul]
      rw [e]
      exact hx
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj σ).injective]

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] {t : Ω}
variable {F L N : IntermediateField (rationalBase k t) Ω}
variable [FiniteDimensional (rationalBase k t) N] [IsGalois (rationalBase k t) N]

attribute [local instance] fieldRingAction

local notation "G" => (N ≃ₐ[rationalBase k t] N)

omit [CharZero k] [IsGalois (rationalBase k t) N] in
private theorem faithfulSMul_normalization [Algebra.IsSeparable (rationalBase k t) N] :
    FaithfulSMul G (coordRing t N) := by
  refine ⟨fun {σ τ} h => ?_⟩
  have hcoeff (b : coordRing t N) : σ (b : N) = τ (b : N) :=
    congrArg (fun c : coordRing t N => (c : N)) (h b)
  letI := fractionFieldRing t N
  ext x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := coordRing t N) x
  rw [map_div₀, map_div₀]
  exact congrArg Subtype.val (congrArg₂ (· / ·) (hcoeff a) (hcoeff b))

theorem isCyclic_normalization_inertia (ht : Transcendental k t)
    (P : Ideal (coordRing t N)) [hP : P.IsMaximal] : IsCyclic (P.inertia G) := by
  letI := dedekindRing t ht N
  letI := faithfulSMul_normalization (N := N)
  haveI : CharZero (IsLocalRing.ResidueField (Localization.AtPrime P)) :=
    charZero_of_injective_algebraMap
      (algebraMap k (IsLocalRing.ResidueField (Localization.AtPrime P))).injective
  exact AbcAdaptation.Reference.Iut.TameInertia.isCyclic_inertia P
    (Ring.ne_bot_of_isMaximal_of_not_isField hP (notFieldRing t ht N))

theorem ramificationIdx_mul_card_inertia (ht : Transcendental k t)
    (hFL : F ≤ L) (hLN : L ≤ N) (P : Ideal (coordRing t N)) [P.IsMaximal] :
    (letI := ringMapAlgebra hFL; (P.comap (ringMap hLN)).ramificationIdx (coordRing t F)) *
        Nat.card ((P.inertia G) ⊓ fixSub N L : Subgroup G) =
      Nat.card ((P.inertia G) ⊓ fixSub N F : Subgroup G) := by
  letI : FiniteDimensional (rationalBase k t) L :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hLN).toLinearMap
      (IntermediateField.inclusion hLN).injective
  letI : Algebra.IsSeparable (rationalBase k t) L :=
    Algebra.IsSeparable.of_algHom (F := rationalBase k t) (E := L) (E' := N)
      (IntermediateField.inclusion hLN)
  letI := dedekindRing t ht L
  have h := ramificationIdx_comp (ringMap hFL).toRingHom
    (ringMap hLN).toRingHom (ringMap_injective hLN) P
  have hcomp : (ringMap hLN).toRingHom.comp (ringMap hFL).toRingHom =
      (ringMap (hFL.trans hLN)).toRingHom := RingHom.ext fun _ => rfl
  rw [hcomp] at h
  rw [← ramificationIdx_eq_card_inertia ht hLN P,
    ← ramificationIdx_eq_card_inertia ht (hFL.trans hLN) P]
  exact h.symm

omit [CharZero k] [FiniteDimensional (rationalBase k t) N] [IsGalois (rationalBase k t) N] in
private theorem ramificationIdx_conjugate (hFL : F ≤ L) (hLN : L ≤ N)
    (m : Ideal (coordRing t F) → ℕ)
    (hm : ∀ w : Ideal (coordRing t L), w.IsMaximal →
      (letI := ringMapAlgebra hFL; w.ramificationIdx (coordRing t F)) =
        m (w.comap (ringMap hFL)))
    (σ : G) (hσ : σ ∈ fixSub N F) (P : Ideal (coordRing t N)) [hP : P.IsMaximal] :
    (letI := ringMapAlgebra hFL; ((σ⁻¹ • P).comap (ringMap hLN)).ramificationIdx (coordRing t F)) =
      (letI := ringMapAlgebra hFL; (P.comap (ringMap hLN)).ramificationIdx (coordRing t F)) := by
  let P' := σ⁻¹ • P
  haveI : P'.IsMaximal := by
    change (σ⁻¹ • P).IsMaximal
    rw [Ideal.pointwise_smul_def]
    exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ _ σ⁻¹)
  have hmax (Q : Ideal (coordRing t N)) [Q.IsMaximal] :
      (Q.comap (ringMap hLN)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (ringMap hLN).toRingHom
      (ringMap_isIntegral hLN) Q
  have hFN := hFL.trans hLN
  have hover : P'.comap (ringMap hFN) = P.comap (ringMap hFN) := by
    ext x
    simp only [Ideal.mem_comap, P', Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    have hx : σ • ringMap hFN x = ringMap hFN x := by
      apply Subtype.ext
      exact (mem_fixSub.mp hσ) _ (x : F).2
    rw [hx]
  have hcomap (Q : Ideal (coordRing t N)) :
      (Q.comap (ringMap hLN)).comap (ringMap hFL) = Q.comap (ringMap hFN) := rfl
  change (letI := ringMapAlgebra hFL; (P'.comap (ringMap hLN)).ramificationIdx (coordRing t F)) = _
  rw [hm _ (hmax P'), hm _ (hmax P), hcomap, hcomap, hover]

private theorem inertia_inf_le_galoisCore (ht : Transcendental k t) (hFL : F ≤ L) (hLN : L ≤ N)
    (m : Ideal (coordRing t F) → ℕ)
    (hm : ∀ w : Ideal (coordRing t L), w.IsMaximal →
      (letI := ringMapAlgebra hFL; w.ramificationIdx (coordRing t F)) =
        m (w.comap (ringMap hFL)))
    (P : Ideal (coordRing t N)) [hP : P.IsMaximal] :
    P.inertia G ⊓ fixSub N L ≤ galoisCore F L := by
  let I := P.inertia G
  let H := fixSub N L
  let K := fixSub N F
  letI : IsCyclic I := isCyclic_normalization_inertia ht P
  rintro τ ⟨hτI, hτH⟩
  rw [mem_galoisCore]
  intro σ hσ
  let P' := σ⁻¹ • P
  haveI : P'.IsMaximal := by
    change (σ⁻¹ • P).IsMaximal
    rw [Ideal.pointwise_smul_def]
    exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ _ σ⁻¹)
  have hK : K.map (MulAut.conj σ⁻¹).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (K.inv_mem hσ))
  have hconjK := card_inertia_inf_map_conj σ⁻¹ K P
  rw [hK] at hconjK
  have hP_ := ramificationIdx_mul_card_inertia ht hFL hLN P
  have hP'_ := ramificationIdx_mul_card_inertia ht hFL hLN P'
  have he := ramificationIdx_conjugate hFL hLN m hm σ hσ P
  change (letI := ringMapAlgebra hFL; (P'.comap (ringMap hLN)).ramificationIdx (coordRing t F)) = _ at he
  rw [he, hconjK] at hP'_
  have hpositive :
      0 < (letI := ringMapAlgebra hFL; (P.comap (ringMap hLN)).ramificationIdx (coordRing t F)) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero, zero_mul] at hP_
    exact Nat.card_pos.ne' hP_.symm
  have hcardL : Nat.card ((P'.inertia G) ⊓ H : Subgroup G) = Nat.card (I ⊓ H : Subgroup G) :=
    Nat.eq_of_mul_eq_mul_left hpositive (hP'_.trans hP_.symm)
  have hconjH := card_inertia_inf_map_conj σ H P'
  have hσP : σ • P' = P := by simp [P']
  rw [hσP, hcardL] at hconjH
  let J := H.map (MulAut.conj σ).toMonoidHom
  have hsub : (I ⊓ J).subgroupOf I = (I ⊓ H).subgroupOf I := by
    apply subgroup_eq_of_card_eq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hconjH
  have hmem : (⟨τ, hτI⟩ : I) ∈ (I ⊓ J).subgroupOf I := by
    rw [hsub]
    exact Subgroup.mem_subgroupOf.mpr ⟨hτI, hτH⟩
  obtain ⟨ρ, hρ, hρτ⟩ := (Subgroup.mem_subgroupOf.mp hmem).2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hρτ
  rw [← hρτ]
  simpa [mul_assoc] using hρ

/-- The Galois closure is unramified over the covering scheme when the original
ramification index depends only on the closed point of the target. -/
theorem galoisClosure_ramificationIdx_eq_one (ht : Transcendental k t)
    (hFL : F ≤ L) (hLN : L ≤ N) (m : Ideal (coordRing t F) → ℕ)
    (hm : ∀ w : Ideal (coordRing t L), w.IsMaximal →
      (letI := ringMapAlgebra hFL; w.ramificationIdx (coordRing t F)) =
        m (w.comap (ringMap hFL)))
    (w : Ideal (coordRing t (galoisClosure (N := N) F L))) (hw : w.IsMaximal) :
    (letI := ringMapAlgebra (le_galoisClosure (F := F) hLN); w.ramificationIdx (coordRing t L)) = 1 := by
  have hMN : galoisClosure (N := N) F L ≤ N := galoisClosure_le
  obtain ⟨P, hP, hPw⟩ := normalization_exists_maximal_over hMN w hw
  letI : P.IsMaximal := hP
  have hfix := inertia_inf_le_galoisCore ht hFL hLN m hm P
  rw [← fixSub_galoisClosure] at hfix
  have hram := (ramificationIdx_eq_one_iff ht (le_galoisClosure (F := F) hLN) hMN P).mpr hfix
  rw [hPw] at hram
  exact hram

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
