/-
Source: Pi1/Orbicurve/HemiTY.lean at revision ca7def953193f861a462aa0831eec8f0a31ff69f.
Original author: Christian Merten and the pi1 contributors.
License: Apache-2.0.
-/
import Solutions.Source_ReferenceIutCanLiftConstantExtensionRamification
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationRamification
import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationSquare

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open Ideal IntermediateField Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin Pointwise

universe u

noncomputable section

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t y : Ω}

/-- The function field generated over the x-line by the other Weierstrass coordinate. -/
abbrev quadraticParameterField (k : Type u) [Field k] [Algebra k Ω] (t y : Ω) :
    IntermediateField (rationalBase k t) Ω :=
  IntermediateField.adjoin (rationalBase k t) {y}

private lemma isIntegral_of_quadraticParameter {b c : Ω} (hb : b ∈ rationalBase k t) (hc : c ∈ rationalBase k t)
    (hy : y ^ 2 + b * y = c) : IsIntegral (rationalBase k t) y := by
  refine ⟨X ^ 2 + (C (⟨b, hb⟩ : rationalBase k t) * X - C (⟨c, hc⟩ : rationalBase k t)), monic_X_pow_add ?_, ?_⟩
  · refine (degree_sub_le _ _).trans_lt ?_
    refine max_lt ((degree_C_mul_X_le _).trans_lt (by norm_num)) ?_
    exact degree_C_le.trans_lt (by norm_num)
  · simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X]
    change y ^ 2 + (b * y - c) = 0
    linear_combination hy

theorem finiteDimensional_quadraticParameterField {b c : Ω} (hb : b ∈ rationalBase k t) (hc : c ∈ rationalBase k t)
    (hy : y ^ 2 + b * y = c) : FiniteDimensional (rationalBase k t) (quadraticParameterField k t y) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral_of_quadraticParameter hb hc hy)

/-- The two roots of the quadratic are both in the adjoined field. -/
private lemma normal_quadraticParameterField [IsAlgClosed Ω] {b c : Ω} (hb : b ∈ rationalBase k t) (hc : c ∈ rationalBase k t)
    (hy : y ^ 2 + b * y = c) : Normal (rationalBase k t) (quadraticParameterField k t y) := by
  let bb : rationalBase k t := ⟨b, hb⟩
  let cc : rationalBase k t := ⟨c, hc⟩
  let Q : (rationalBase k t)[X] := X ^ 2 + (C bb * X - C cc)
  have hQ0 : Q ≠ 0 := by
    intro h
    have := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_zero] at this
    have hd : Q.natDegree = 2 := by
      apply Polynomial.natDegree_eq_of_degree_eq_some
      rw [Polynomial.degree_add_eq_left_of_degree_lt]
      · simp
      · rw [Polynomial.degree_X_pow]
        refine (degree_sub_le _ _).trans_lt ?_
        refine max_lt ((degree_C_mul_X_le _).trans_lt (by norm_num)) ?_
        exact degree_C_le.trans_lt (by norm_num)
    omega
  have hev : ∀ z : Ω, aeval z Q = z ^ 2 + b * z - c := by
    intro z
    simp only [Q, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C]
    change _ = z ^ 2 + (algebraMap (rationalBase k t) Ω bb) * z - (algebraMap (rationalBase k t) Ω cc)
    ring
  have hyQ : aeval y Q = 0 := by rw [hev]; linear_combination hy
  have hymem : y ∈ quadraticParameterField k t y := IntermediateField.subset_adjoin _ _ rfl
  have hroots : Q.rootSet Ω ⊆ quadraticParameterField k t y := by
    intro z hz
    rw [Polynomial.mem_rootSet, hev] at hz
    obtain ⟨-, hz⟩ := hz
    have hz' : (z - y) * (z + y + b) = 0 := by linear_combination hz - hy
    have hbmem : b ∈ quadraticParameterField k t y := (quadraticParameterField k t y).algebraMap_mem bb
    rcases mul_eq_zero.mp hz' with h | h
    · rw [sub_eq_zero.mp h]; exact hymem
    · have : z = -y - b := by linear_combination h
      rw [this]
      exact sub_mem (neg_mem hymem) hbmem
  have heq : IntermediateField.adjoin (rationalBase k t) (Q.rootSet Ω) = quadraticParameterField k t y := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]; exact hroots
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      apply IntermediateField.subset_adjoin
      rw [Polynomial.mem_rootSet]
      exact ⟨hQ0, hyQ⟩
  haveI hs := IntermediateField.adjoin_rootSet_isSplittingField (K := rationalBase k t) (L := Ω) (p := Q)
    (IsAlgClosed.splits _)
  rw [heq] at hs
  exact Normal.of_isSplittingField Q

theorem isGalois_quadraticParameterField [IsAlgClosed Ω] [CharZero k] {b c : Ω}
    (hb : b ∈ rationalBase k t) (hc : c ∈ rationalBase k t) (hy : y ^ 2 + b * y = c) :
    IsGalois (rationalBase k t) (quadraticParameterField k t y) := by
  letI : FiniteDimensional (rationalBase k t) (quadraticParameterField k t y) :=
    finiteDimensional_quadraticParameterField hb hc hy
  letI : CharZero (rationalBase k t) :=
    charZero_of_injective_algebraMap (algebraMap k (rationalBase k t)).injective
  letI : Normal (rationalBase k t) (quadraticParameterField k t y) :=
    normal_quadraticParameterField hb hc hy
  letI : Algebra.IsSeparable (rationalBase k t) (quadraticParameterField k t y) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact IsGalois.mk

/-- The multiplicity of the sign quotient at a prime of the x-line. -/
abbrev signQuotientMultiplicity [CharZero k] (t y : Ω)
    (v : Ideal (coordRing t (⊥ : IntermediateField (rationalBase k t) Ω))) : ℕ :=
  ramificationMultiplicity (bot_le :
    (⊥ : IntermediateField (rationalBase k t) Ω) ≤ quadraticParameterField k t y) v

attribute [local instance] fieldRingAction

/-- At a closed point of the quadratic normalization, the sign multiplicity is its
ramification index over the line. -/
theorem signQuotientMultiplicity_eq_index [CharZero k]
    [FiniteDimensional (rationalBase k t) (quadraticParameterField k t y)]
    [IsGalois (rationalBase k t) (quadraticParameterField k t y)]
    (ht : Transcendental k t) (w : Ideal (coordRing t (quadraticParameterField k t y)))
    (hw : w.IsMaximal) :
    ramificationIndex (bot_le :
      (⊥ : IntermediateField (rationalBase k t) Ω) ≤ quadraticParameterField k t y) w =
      signQuotientMultiplicity t y (w.comap (ringMap (bot_le :
        (⊥ : IntermediateField (rationalBase k t) Ω) ≤ quadraticParameterField k t y))) := by
  let N := quadraticParameterField k t y
  let h : (⊥ : IntermediateField (rationalBase k t) Ω) ≤ N := bot_le
  letI := ringMapAlgebra h
  letI := normalizationGaloisGroup_fixSub h ht
  letI : Finite (fixSub N ⊥) := inferInstance
  letI : w.IsPrime := hw.isPrime
  let v := w.comap (ringMap h)
  letI : w.LiesOver v := ⟨rfl⟩
  exact (Ideal.ramificationIdxIn_eq_ramificationIdx v w (fixSub N ⊥)).symm

section ConstantExtension

variable {K : Type u} [Field K] [Algebra k K] [Algebra K Ω] [IsScalarTower k K Ω]

private lemma rationalBase_range_subset_quadraticParameterField :
    Set.range (algebraMap (rationalBase k t) Ω) ⊆
      (quadraticParameterField K t y : Set Ω) := by
  rintro _ ⟨c, rfl⟩
  let c' : rationalBase K t := rationalBaseMap (k := k) (K := K) t c
  have hmap : algebraMap (rationalBase K t) Ω c' = algebraMap (rationalBase k t) Ω c :=
    rfl
  rw [← hmap]
  exact (quadraticParameterField K t y).algebraMap_mem c'

theorem quadraticParameterField_mem_extension :
    ∀ x ∈ quadraticParameterField k t y, x ∈ quadraticParameterField K t y := by
  have hgen : ({y} : Set Ω) ⊆ (quadraticParameterField K t y : Set Ω) :=
    IntermediateField.subset_adjoin (rationalBase K t) ({y} : Set Ω)
  have hsubset : (quadraticParameterField k t y : Set Ω) ⊆
      (quadraticParameterField K t y : Set Ω) :=
    (IntermediateField.adjoin_subset_adjoin_iff (F := rationalBase k t)
      (F' := rationalBase K t) (S := ({y} : Set Ω)) (S' := ({y} : Set Ω))).mpr
      ⟨rationalBase_range_subset_quadraticParameterField (k := k) (K := K) (t := t) (y := y), hgen⟩
  exact fun _ hx => hsubset hx

theorem quadraticParameterField_le_extension_adjoin :
    quadraticParameterField K t y ≤
      IntermediateField.adjoin (rationalBase K t) (quadraticParameterField k t y : Set Ω) := by
  apply IntermediateField.adjoin_simple_le_iff.mpr
  exact IntermediateField.subset_adjoin _ _
    (IntermediateField.mem_adjoin_simple_self (rationalBase k t) y)

/-- The sign quotient multiplicity at a closed prime with nonzero contraction descends
to the corresponding closed prime over the smaller constant field. -/
theorem signQuotientMultiplicity_constantExtension [IsAlgClosed Ω] [CharZero k] [CharZero K]
    (htK : Transcendental K t) {b c : Ω}
    (hb : b ∈ rationalBase k t) (hc : c ∈ rationalBase k t) (hy : y ^ 2 + b * y = c)
    (v' : Ideal (coordRing t (⊥ : IntermediateField (rationalBase K t) Ω))) (hv' : v'.IsMaximal)
    (hv₀ : v'.comap (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K))) ≠ ⊥) :
    signQuotientMultiplicity t y v' =
      signQuotientMultiplicity t y
        (v'.comap (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K)))) := by
  let N := quadraticParameterField k t y
  let N' := quadraticParameterField K t y
  let h : (⊥ : IntermediateField (rationalBase k t) Ω) ≤ N := bot_le
  let h' : (⊥ : IntermediateField (rationalBase K t) Ω) ≤ N' := bot_le
  let hN : ∀ x ∈ N, x ∈ N' := quadraticParameterField_mem_extension
  have ht : Transcendental k t := transcendental_of_constantExtension htK
  have hbK : b ∈ rationalBase K t := mem_rationalBase_extension hb
  have hcK : c ∈ rationalBase K t := mem_rationalBase_extension hc
  letI : FiniteDimensional (rationalBase k t) N := finiteDimensional_quadraticParameterField hb hc hy
  letI : FiniteDimensional (rationalBase K t) N' :=
    finiteDimensional_quadraticParameterField hbK hcK hy
  letI : IsGalois (rationalBase k t) N := isGalois_quadraticParameterField hb hc hy
  letI : IsGalois (rationalBase K t) N' := isGalois_quadraticParameterField hbK hcK hy
  obtain ⟨w', hw', hw'v⟩ := normalization_exists_maximal_over h' v' hv'
  letI := hw'
  let w := w'.comap (constantExtensionMap hN)
  have hcomap : v'.comap (constantExtensionMap (bot_mem_constantExtension (k := k) (K := K))) =
      w.comap (ringMap h) := by
    rw [← hw'v]
    ext x
    exact Iff.rfl
  have hw₀ : w ≠ ⊥ := by
    intro hw
    apply hv₀
    rw [hcomap, hw]
    exact Ideal.comap_bot_of_injective _ (ringMap_injective h)
  letI : w.IsPrime := Ideal.comap_isPrime _ _
  letI := dedekindRing t ht N
  have hw : w.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hw₀
  have he := ramificationIdx_constantExtension_eq htK h h' bot_mem_constantExtension hN bot_le
    quadraticParameterField_le_extension_adjoin w' hw₀
  calc
    signQuotientMultiplicity t y v' = ramificationIndex h' w' := by
      rw [← hw'v]
      exact (signQuotientMultiplicity_eq_index htK w' hw').symm
    _ = ramificationIndex h w := he
    _ = signQuotientMultiplicity t y (w.comap (ringMap h)) :=
      signQuotientMultiplicity_eq_index ht w hw
    _ = _ := congrArg (signQuotientMultiplicity t y) hcomap.symm

end ConstantExtension

end

end JoshiTeich.Act1Scene1.FunctionFieldNormalization
