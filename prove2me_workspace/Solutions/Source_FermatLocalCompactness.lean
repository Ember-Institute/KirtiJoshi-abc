/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Source port: Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1.
Original notices retained. See source-ledger.json for exact paths and hashes.
-/
import Solutions.Source_FermatLocalCompactnessBridge

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper.Source

open Local Filter Topology
open scoped Classical IntermediateField

/-! ### The main compactness statement -/

section Main

/-- Primes carry their primality as an instance (local). -/
local instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- **The compactness argument of [GenEll], Theorem 2.1**: for points `x_n` of degree `≤ d` and a
finite set `V` of primes, there are a subsequence and a finite set `T` of places of `M.K` (the
algebraic limit points at the places of `V ∪ {∞}`) such that every `φ ≠ 0, 1` regular and
invertible, with `φ − 1` invertible, at the places of `T` has values at all embeddings of the
fields of definition into `ℂ` and into `ℚ̄_p` (`p ∈ V`) bounded away from `0`, `1`, `∞`, along a
tail of the subsequence. -/
theorem exists_subseq_bounded {N : ℕ} (M : Model N) (hRF : ResiduesFinite M)
    (V : Finset Nat.Primes) {d : ℕ} (x : ℕ → QbarPoint M.K)
    (hx : ∀ n, (x n).degree ≤ d) :
    ∃ D : ℕ → ℕ, StrictMono D ∧ ∃ T : Finset (Place M.K), ∀ φ : M.K, φ ≠ 0 → φ ≠ 1 →
      (∀ P ∈ T, φ ∈ P.1 ∧ φ⁻¹ ∈ P.1 ∧ (φ - 1)⁻¹ ∈ P.1) →
      ∃ C : ℝ, ∀ᶠ n in atTop, ∃ hφ : φ ∈ (x (D n)).P.1,
        (x (D n)).eval φ hφ ≠ 0 ∧ (x (D n)).eval φ hφ ≠ 1 ∧
        (∀ σ : (x (D n)).fieldOf →+* ℂ,
          |Real.log ‖σ (evalF (x (D n)) ⟨φ, hφ⟩)‖| ≤ C ∧
          |Real.log ‖σ (evalF (x (D n)) ⟨φ, hφ⟩) - 1‖| ≤ C) ∧
        ∀ p ∈ V, ∀ τ : (x (D n)).fieldOf →+* PadicAlgCl (p : ℕ),
          |Real.log ‖τ (evalF (x (D n)) ⟨φ, hφ⟩)‖| ≤ C ∧
          |Real.log ‖τ (evalF (x (D n)) ⟨φ, hφ⟩) - 1‖| ≤ C := by
  letI : Countable M.K := model_countable M
  letI (n : ℕ) : FiniteDimensional ℚ (x n).fieldOf := pointFieldFinite M hRF (x n)
  letI (n : ℕ) : NumberField (x n).fieldOf := {}
  have hd : 0 < d := lt_of_lt_of_le (Module.finrank_pos (R := ℚ) (M := (x 0).fieldOf)) (hx 0)
  haveI : NeZero d := ⟨hd.ne'⟩
  -- enumerate the embeddings
  choose eC heC using fun n => exists_surj_embeddings (E := ℂ) (x n) (hx n)
  choose eP heP using fun (p : Nat.Primes) n =>
    exists_surj_embeddings (E := PadicAlgCl (p : ℕ)) (x n) (hx n)
  set yC : ℕ → Fin d → EPlace M.K ℂ := fun n i => pointEPlace (x n) (eC n i) with hyC
  set yP : ∀ p : Nat.Primes, ℕ → Fin d → EPlace M.K (PadicAlgCl (p : ℕ)) :=
    fun p n i => pointEPlace (x n) (eP p n i) with hyP
  have hQ : ∀ n (q : ℚ), (q : M.K) ∈ (x n).P.1 := fun n q => (x n).P.2.2 q
  have hgoodP : ∀ (p : Nat.Primes) n i f α, (yP p n i).val f = some α →
      (minpoly ℚ_[(p : ℕ)] α).natDegree ≤ d := by
    intro p n i f α h
    obtain ⟨hf, rfl⟩ := (EPlace.val_eq_some_iff _).mp h
    exact (natDegree_minpoly_padic_le _ _).trans (hx n)
  -- successive rounds
  have key : ∀ W : Finset Nat.Primes, ∃ D : ℕ → ℕ, StrictMono D ∧
      (∃ ξ : Fin d → M.K → Option ℂ, ∀ i f, TendstoP1 (fun n => (yC (D n) i).val f) (ξ i f)) ∧
      ∀ p ∈ W, ∃ ξ : Fin d → M.K → Option (PadicAlgCl (p : ℕ)),
        ∀ i f, TendstoP1 (fun n => (yP p (D n) i).val f) (ξ i f) := by
    intro W
    induction W using Finset.induction_on with
    | empty =>
      obtain ⟨D, hD, -, ξ, hξ⟩ := exists_subseq_limit (Good := fun _ : ℂ => True)
        (fun a _ => exists_tendsto_or_tendsto_norm_atTop a) yC (fun _ _ _ _ _ => trivial)
        id strictMono_id
      exact ⟨D, hD, ⟨ξ, hξ⟩, by simp⟩
    | insert p W hpW ih =>
      obtain ⟨D, hD, ⟨ξC, hξC⟩, hW⟩ := ih
      obtain ⟨D', hD', ⟨ψ, hψ, rfl⟩, ξ, hξ⟩ :=
        exists_subseq_limit (Good := fun α : PadicAlgCl (p : ℕ) =>
          (minpoly ℚ_[(p : ℕ)] α).natDegree ≤ d)
          (fun a ha => PadicAlgCl.exists_tendsto_or_tendsto_norm_atTop d a ha) (yP p)
          (hgoodP p) D hD
      refine ⟨D ∘ ψ, hD', ⟨ξC, fun i f => tendstoP1_comp_subseq (hξC i f) hψ⟩, ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hqW
      · exact ⟨ξ, hξ⟩
      · obtain ⟨ξq, hξq⟩ := hW q hqW
        exact ⟨ξq, fun i f => tendstoP1_comp_subseq (hξq i f) hψ⟩
  obtain ⟨D, hD, ⟨ξC, hC⟩, hPV⟩ := key V
  choose ξP hξP using hPV
  have hQC : ∀ i n (q : ℚ), (q : M.K) ∈ (yC (D n) i).O := fun i n q => hQ (D n) q
  have hQP : ∀ p i n (q : ℚ), (q : M.K) ∈ (yP p (D n) i).O := fun p i n q => hQ (D n) q
  -- the limit places
  set T : Finset (Place M.K) :=
    (Finset.univ.biUnion fun i => (limitPlace (hQC i) (hC i)).toFinset) ∪
      V.attach.biUnion fun p => Finset.univ.biUnion fun i =>
        (limitPlace (hQP p.1 i) (hξP p.1 p.2 i)).toFinset with hT
  refine ⟨D, hD, T, fun φ hφ0 hφ1 hφT => ?_⟩
  have hbC : ∀ i, ∃ C : ℝ, ∀ᶠ n in atTop, ∃ α, (yC (D n) i).val φ = some α ∧
      |Real.log ‖α‖| ≤ C ∧ |Real.log ‖α - 1‖| ≤ C ∧ α ≠ 0 ∧ α ≠ 1 := fun i =>
    eventually_bounded_of_limitPlace (hQC i) (hC i) hφ0 hφ1 fun P hP => hφT P (by
      rw [hT, Finset.mem_union, Finset.mem_biUnion]
      exact Or.inl ⟨i, Finset.mem_univ _, by simp [hP]⟩)
  have hbP : ∀ p : V, ∀ i, ∃ C : ℝ, ∀ᶠ n in atTop, ∃ α, (yP p.1 (D n) i).val φ = some α ∧
      |Real.log ‖α‖| ≤ C ∧ |Real.log ‖α - 1‖| ≤ C ∧ α ≠ 0 ∧ α ≠ 1 := fun p i =>
    eventually_bounded_of_limitPlace (hQP p.1 i) (hξP p.1 p.2 i) hφ0 hφ1 fun P hP => hφT P (by
      rw [hT, Finset.mem_union, Finset.mem_biUnion]
      right
      rw [Finset.mem_biUnion]
      exact ⟨p, Finset.mem_attach _ _, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [hP]⟩⟩)
  choose CC hCC using hbC
  choose CP hCP using hbP
  set C : ℝ := ∑ i, |CC i| + ∑ p ∈ V.attach, ∑ i, |CP p i| with hCdef
  have hCC_le : ∀ i, CC i ≤ C := fun i => by
    have h1 : |CC i| ≤ ∑ i, |CC i| :=
      Finset.single_le_sum (f := fun i => |CC i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ p ∈ V.attach, ∑ i, |CP p i| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [le_abs_self (CC i)]
  have hCP_le : ∀ p i, CP p i ≤ C := fun p i => by
    have h1 : |CP p i| ≤ ∑ i, |CP p i| :=
      Finset.single_le_sum (f := fun i => |CP p i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i, |CP p i| ≤ ∑ p ∈ V.attach, ∑ i, |CP p i| :=
      Finset.single_le_sum (f := fun p => ∑ i, |CP p i|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_attach _ p)
    have h3 : 0 ≤ ∑ i, |CC i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [le_abs_self (CP p i)]
  refine ⟨C, ?_⟩
  have hevC := Filter.eventually_all.mpr hCC
  have hevP : ∀ᶠ n in atTop, ∀ p ∈ V.attach, ∀ i, ∃ α, (yP p.1 (D n) i).val φ = some α ∧
      |Real.log ‖α‖| ≤ CP p i ∧ |Real.log ‖α - 1‖| ≤ CP p i ∧ α ≠ 0 ∧ α ≠ 1 :=
    (Filter.eventually_all_finset _).mpr fun p _ => Filter.eventually_all.mpr (hCP p)
  filter_upwards [hevC, hevP] with n hnC hnP
  obtain ⟨α₀, hα₀, -, -, hα₀0, hα₀1⟩ := hnC ⟨0, hd⟩
  obtain ⟨hφmem, hα₀eq⟩ := (EPlace.val_eq_some_iff _).mp hα₀
  have hv0 : evalF (x (D n)) ⟨φ, hφmem⟩ ≠ 0 := fun h0 => hα₀0 (by
    rw [← hα₀eq]
    change eC (D n) ⟨0, hd⟩ (evalF (x (D n)) ⟨φ, hφmem⟩) = 0
    rw [h0, map_zero])
  have hv1 : evalF (x (D n)) ⟨φ, hφmem⟩ ≠ 1 := fun h0 => hα₀1 (by
    rw [← hα₀eq]
    change eC (D n) ⟨0, hd⟩ (evalF (x (D n)) ⟨φ, hφmem⟩) = 1
    rw [h0, map_one])
  refine ⟨hφmem, (fun h0 => hv0 (Subtype.ext h0)),
    (fun h1 => hv1 (Subtype.ext h1)), fun σ => ?_, fun p hp τ => ?_⟩
  · obtain ⟨i, rfl⟩ := heC (D n) σ
    obtain ⟨α, hα, h1, h2, -, -⟩ := hnC i
    rw [show (yC (D n) i).val φ = some (eC (D n) i (evalF (x (D n)) ⟨φ, hφmem⟩)) from
      pointEPlace_val_of_mem _ _ hφmem] at hα
    cases hα
    exact ⟨h1.trans (hCC_le i), h2.trans (hCC_le i)⟩
  · obtain ⟨i, rfl⟩ := heP p (D n) τ
    obtain ⟨α, hα, h1, h2, -, -⟩ := hnP ⟨p, hp⟩ (Finset.mem_attach _ _) i
    rw [show (yP p (D n) i).val φ = some (eP p (D n) i (evalF (x (D n)) ⟨φ, hφmem⟩)) from
      pointEPlace_val_of_mem _ _ hφmem] at hα
    cases hα
    exact ⟨h1.trans (hCP_le ⟨p, hp⟩ i), h2.trans (hCP_le ⟨p, hp⟩ i)⟩

end Main


/-- The fixed support is exactly `{2}`; every full point-field embedding is retained. -/
theorem localCompactness_source {N : ℕ} (M : Model N) (hRF : ResiduesFinite M) :
    LocalCompactness M := by
  intro d xs hxs
  let V : Finset Nat.Primes := {⟨2, Nat.prime_two⟩}
  obtain ⟨s, hs, T, hT⟩ := exists_subseq_bounded M hRF V xs hxs
  refine ⟨s, hs, T, fun φ h0 h1 hφT => ?_⟩
  obtain ⟨c, hc⟩ := hT φ h0 h1 hφT
  refine ⟨c, ?_⟩
  filter_upwards [hc] with n hn
  obtain ⟨hφ, hv0, hv1, hC, hP⟩ := hn
  refine ⟨hφ, hv0, hv1, ?_, ?_⟩
  · exact hC
  · exact hP ⟨2, Nat.prime_two⟩ (Finset.mem_singleton_self _)

end AbcAdaptation.Tripod.Fermat.Proper.Source
