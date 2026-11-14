/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Source port: Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1.
Original notices retained. See source-ledger.json for exact paths and hashes.
-/
import Definitions.Def_FermatLocalBelyi
import Solutions.Source_FermatLocalSequence
import Solutions.Source_FermatLocalLimitValuation
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.LinearAlgebra.Countable
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper.Source

open Local Filter Topology
open scoped Classical IntermediateField

variable {K : Type*} [Field K] [CharZero K]

/-- Evaluation lands in the actual full residue-image field, as in the fixed carrier. -/
noncomputable def evalF (x : QbarPoint K) : x.P.1 →+* x.fieldOf :=
  (x.σ.comp x.P.residue).codRestrict x.fieldOf fun f =>
    x.eval_mem_fieldOf f.1 f.2

@[simp] theorem coe_evalF (x : QbarPoint K) (f : x.P.1) :
    (evalF x f : Qbar) = x.eval f.1 f.2 := rfl

/-- The finite-dimensionality input is exactly the pre-existing `hRF`. -/
theorem pointFieldFinite {N : ℕ} (M : Model N) (hRF : ResiduesFinite M)
    (x : QbarPoint M.K) : FiniteDimensional ℚ x.fieldOf := by
  letI : FiniteDimensional ℚ x.P.ResidueField := hRF x.P
  exact x.σ.toRatAlgHom.equivFieldRange.toLinearEquiv.finiteDimensional

section EPlaces

variable {E : Type*} [NormedField E]

/-- A complete point-field embedding gives a genuine valued place. -/
noncomputable def pointEPlace (x : QbarPoint K) (τ : x.fieldOf →+* E) : EPlace K E where
  O := x.P.1
  ψ := τ.comp (evalF x)
  eq_zero_iff f := by
    change τ (evalF x f) = 0 ↔ ¬ IsUnit f
    rw [map_eq_zero_iff τ τ.injective]
    have heval : evalF x f = 0 ↔ x.P.residue f = 0 := by
      constructor
      · intro h
        apply x.σ.injective
        have hz : (evalF x f : Qbar) = 0 :=
          congrArg (fun a : x.fieldOf => (a : Qbar)) h
        exact (coe_evalF x f).symm.trans (hz.trans (map_zero x.σ).symm)
      · intro h
        apply Subtype.ext
        change x.σ (x.P.residue f) = 0
        rw [h, map_zero]
    rw [heval]
    change Ideal.Quotient.mk (IsLocalRing.maximalIdeal x.P.1) f = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem pointEPlace_val_of_mem (x : QbarPoint K) (τ : x.fieldOf →+* E) {f : K}
    (hf : f ∈ x.P.1) : (pointEPlace x τ).val f = some (τ (evalF x ⟨f, hf⟩)) :=
  EPlace.val_of_mem _ hf

end EPlaces

/-- The degree over `ℚ_p` of the image of an algebraic number of degree `≤ d`. -/
theorem natDegree_minpoly_padic_le {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [NumberField F]
    (τ : F →+* PadicAlgCl p) (a : F) :
    (minpoly ℚ_[p] (τ a)).natDegree ≤ Module.finrank ℚ F := by
  have hint : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  have hne : (minpoly ℚ a).map (algebraMap ℚ ℚ_[p]) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint)
  have hdvd : minpoly ℚ_[p] (τ a) ∣ (minpoly ℚ a).map (algebraMap ℚ ℚ_[p]) := by
    refine minpoly.dvd _ _ ?_
    rw [Polynomial.aeval_map_algebraMap]
    have := congrArg τ.toRatAlgHom (minpoly.aeval ℚ a)
    rw [map_zero, ← Polynomial.aeval_algHom_apply] at this
    exact this
  calc (minpoly ℚ_[p] (τ a)).natDegree
      ≤ ((minpoly ℚ a).map (algebraMap ℚ ℚ_[p])).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hne
    _ = (minpoly ℚ a).natDegree := Polynomial.natDegree_map _
    _ ≤ Module.finrank ℚ F := minpoly.natDegree_le a

/-- Countability follows from the finite simple-function-field presentation in `M`. -/
theorem model_countable {N : ℕ} (M : Model N) : Countable M.K := by
  let t : M.K := M.u
  haveI : FiniteDimensional ℚ⟮t⟯ M.K := M.finite_u
  haveI : Countable (Polynomial ℚ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Polynomial.cardinalMk_le_max (R := ℚ)).trans (by simp)
  haveI : Countable ℚ⟮t⟯ := by
    have hsurj : Function.Surjective fun pq : Polynomial ℚ × Polynomial ℚ =>
        (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) pq.1 /
          Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) pq.2 : ℚ⟮t⟯) := by
      rintro ⟨y, hy⟩
      obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff ℚ y).mp hy
      refine ⟨(r, s), Subtype.ext ?_⟩
      change ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) r : ℚ⟮t⟯) : M.K) /
          ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) s : ℚ⟮t⟯) : M.K) = _
      have h1 : ∀ f : Polynomial ℚ,
          ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ t) f : ℚ⟮t⟯) : M.K) =
            Polynomial.aeval t f := fun f => by
        have := Polynomial.aeval_algHom_apply (IntermediateField.val ℚ⟮t⟯)
          (IntermediateField.AdjoinSimple.gen ℚ t) f
        exact this.symm
      rw [h1, h1]
    exact hsurj.countable
  exact Finsupp.Countable.of_moduleFinite (R := ℚ⟮t⟯) (M := M.K)

/-! ### Enumerating embeddings -/

/-- A surjection `Fin d → (ℚ(x) →+* E)` onto the embeddings of the field of definition of a
point of degree `≤ d`. -/
theorem exists_surj_embeddings {E : Type*} [Field E] [CharZero E] [IsAlgClosed E]
    (x : QbarPoint K) [FiniteDimensional ℚ x.fieldOf] {d : ℕ} (hd : x.degree ≤ d) :
    ∃ e : Fin d → (x.fieldOf →+* E), Function.Surjective e := by
  letI : NumberField x.fieldOf := {}
  have hcard : Fintype.card (x.fieldOf →+* E) ≤ d := by
    rw [NumberField.Embeddings.card]
    exact hd
  haveI : Nonempty (x.fieldOf →+* E) := inferInstance
  refine ⟨fun i => if h : (i : ℕ) < Fintype.card (x.fieldOf →+* E) then
      (Fintype.equivFin (x.fieldOf →+* E)).symm ⟨i, h⟩ else Classical.arbitrary _, fun τ => ?_⟩
  set j := Fintype.equivFin (x.fieldOf →+* E) τ
  refine ⟨⟨j, lt_of_lt_of_le j.2 hcard⟩, ?_⟩
  simp only [j.2, dif_pos]
  exact (Fintype.equivFin (x.fieldOf →+* E)).symm_apply_apply τ

/-! ### Limit places -/

section LimitPlaces

variable {E : Type*} [NormedField E] [CharZero E]

/-- `E`-valued places map rational numbers to themselves. -/
theorem EPlace.val_ratCast (y : EPlace K E) (hQ : ∀ q : ℚ, (q : K) ∈ y.O) (q : ℚ) :
    y.val (q : K) = some (q : E) := by
  rw [EPlace.val_of_mem y (hQ q)]
  congr 1
  have hden : ((q.den : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have h1 : y.ψ ⟨(q : K), hQ q⟩ * (q.den : E) = (q.num : E) := by
    have h2 : (⟨(q : K), hQ q⟩ : y.O) * (q.den : y.O) = (q.num : y.O) := by
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, SubringClass.coe_natCast, SubringClass.coe_intCast]
      exact_mod_cast Rat.mul_den_eq_num q
    have := congrArg y.ψ h2
    rwa [map_mul, map_natCast, map_intCast] at this
  have hq : (q : E) = (q.num : E) / (q.den : E) := Rat.cast_def q
  rw [hq, eq_div_iff hden]
  exact h1

variable {y : ℕ → EPlace K E} {ξ : K → Option E}

/-- The limit of a convergent sequence of `E`-valued places with `ℚ ⊆ O` contains `ℚ`. -/
theorem ratCast_mem_limitSubring (hQ : ∀ n (q : ℚ), (q : K) ∈ (y n).O)
    (h : ∀ f, TendstoP1 (fun n => (y n).val f) (ξ f)) (q : ℚ) : (q : K) ∈ limitSubring h := by
  rw [mem_limitSubring]
  have : ξ (q : K) = some (q : E) := (h (q : K)).unique
    ((tendstoP1_some_iff' (E := E)).mpr ⟨fun _ => (q : E),
      Eventually.of_forall fun n => EPlace.val_ratCast (y n) (hQ n) q, tendsto_const_nhds⟩)
  rw [this]
  exact Option.some_ne_none _

/-- The limit place (if the limit valuation ring is not everything). -/
noncomputable def limitPlace (hQ : ∀ n (q : ℚ), (q : K) ∈ (y n).O)
    (h : ∀ f, TendstoP1 (fun n => (y n).val f) (ξ f)) : Option (Place K) :=
  if hT : limitSubring h = ⊤ then none
  else some ⟨limitSubring h, hT, ratCast_mem_limitSubring hQ h⟩

/-- **Bounds away from `0`, `1`, `∞` along a convergent sequence**, for a function which is
regular, invertible, and with `φ − 1` invertible, at the limit place. -/
theorem eventually_bounded_of_limitPlace (hQ : ∀ n (q : ℚ), (q : K) ∈ (y n).O)
    (h : ∀ f, TendstoP1 (fun n => (y n).val f) (ξ f)) {φ : K} (hφ0 : φ ≠ 0) (hφ1 : φ ≠ 1)
    (hP : ∀ P, limitPlace hQ h = some P → φ ∈ P.1 ∧ φ⁻¹ ∈ P.1 ∧ (φ - 1)⁻¹ ∈ P.1) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∃ α, (y n).val φ = some α ∧
      |Real.log ‖α‖| ≤ C ∧ |Real.log ‖α - 1‖| ≤ C ∧ α ≠ 0 ∧ α ≠ 1 := by
  have hmem : ∀ g, (g = φ ∨ g = φ⁻¹ ∨ g = (φ - 1)⁻¹) → ξ g ≠ none := by
    intro g hg
    rw [← mem_limitSubring h]
    by_cases hT : limitSubring h = ⊤
    · rw [hT]
      exact ValuationSubring.mem_top g
    · have := hP ⟨limitSubring h, hT, ratCast_mem_limitSubring hQ h⟩ (by
        simp only [limitPlace, dif_neg hT])
      rcases hg with rfl | rfl | rfl
      · exact this.1
      · exact this.2.1
      · exact this.2.2
  obtain ⟨β, hβ⟩ := Option.ne_none_iff_exists'.mp (hmem φ (Or.inl rfl))
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact hmem φ⁻¹ (Or.inr (Or.inl rfl)) (limit_inv_of_eq_zero h hφ0 hβ)
  have hβ1 : β ≠ 1 := by
    rintro rfl
    have hm1 : ξ (-1) = some (-1) := limit_neg h (limit_one h)
    have h2 : ξ (φ - 1) = some 0 := by
      rw [sub_eq_add_neg, limit_add h hβ hm1, add_neg_cancel]
    exact hmem (φ - 1)⁻¹ (Or.inr (Or.inr rfl))
      (limit_inv_of_eq_zero h (sub_ne_zero.mpr hφ1) h2)
  exact eventually_abs_log_le h hβ hβ0 hβ1

end LimitPlaces

/-! ### The subsequence -/

section Subsequence

/-- One round of the diagonal argument, along a given subsequence. -/
theorem exists_subseq_limit [Countable K] {E : Type*} [NormedField E] {Good : E → Prop}
    (hcpt : ∀ a : ℕ → E, (∀ n, Good (a n)) → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ b, Tendsto (a ∘ φ) atTop (𝓝 b)) ∨ Tendsto (fun n => ‖a (φ n)‖) atTop atTop))
    {d : ℕ} [NeZero d] (y : ℕ → Fin d → EPlace K E)
    (hgood : ∀ n i f α, (y n i).val f = some α → Good α) (D₀ : ℕ → ℕ) (hD₀ : StrictMono D₀) :
    ∃ D : ℕ → ℕ, StrictMono D ∧ (∃ ψ : ℕ → ℕ, StrictMono ψ ∧ D = D₀ ∘ ψ) ∧
      ∃ ξ : Fin d → K → Option E, ∀ i f, TendstoP1 (fun n => (y (D n) i).val f) (ξ i f) := by
  obtain ⟨ψ, hψ, ξ, hξ⟩ := exists_limit hcpt (fun n => y (D₀ n))
    (fun n i f α h => hgood _ _ _ _ h)
  exact ⟨D₀ ∘ ψ, hD₀.comp hψ, ⟨ψ, hψ, rfl⟩, ξ, hξ⟩

/-- Convergence is preserved along further subsequences. -/
theorem tendstoP1_comp_subseq {E : Type*} [NormedField E] {a : ℕ → Option E} {b : Option E}
    (h : TendstoP1 a b) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) : TendstoP1 (a ∘ ψ) b :=
  h.comp_of_tendsto hψ.tendsto_atTop

end Subsequence


end AbcAdaptation.Tripod.Fermat.Proper.Source
