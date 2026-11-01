import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltField
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
source-id: JT-SCENE1-GEOMETRIC-TILT-COMPARISON
source: Joshi II `se:ff-rings`, with its fixed field F = C_p^flat;
the actual completed coefficient-field norm-power comparison.
fidelity: the generic consumer of a proved field equivalence and its norm-power
identity constructs the integer-ring, mod-p, pretilt and fraction-field
equivalences. It proves the same power identity for both actual tilt valuations.
The hypotheses are the comparison theorem consumed by this generic lemma, not
additional source laws for an InitialThetaData instance. Original proofs.
boundary: Scene1/Derived; the actual coefficient-field comparison must supply
the equivalence and its norm identity. Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.GeometricTiltComparison

open scoped NNReal
noncomputable section
universe u v
variable {Ω : Type u} {Ψ : Type v}
variable [NormedField Ω] [IsUltrametricDist Ω]
variable [NormedField Ψ] [IsUltrametricDist Ψ]
variable (e : Ω ≃+* Ψ) (d : ℕ) (hd : 0 < d)
variable (hnorm : ∀ x : Ω, ‖e x‖ ^ d = ‖x‖)

def integerEquiv : LocalGeometricFontaine.integerRing Ω ≃+*
    LocalGeometricFontaine.integerRing Ψ where
  toFun x := ⟨e x, (LocalGeometricFontaine.mem_integerRing Ψ _).mpr
    ((pow_le_one_iff_of_nonneg (norm_nonneg _) hd.ne').mp
      ((hnorm x).trans_le ((LocalGeometricFontaine.mem_integerRing Ω _).mp x.property)))⟩
  invFun y := ⟨e.symm y, (LocalGeometricFontaine.mem_integerRing Ω _).mpr (by
    have h := hnorm (e.symm y)
    rw [e.apply_symm_apply] at h
    exact h.symm.trans_le (pow_le_one₀ (norm_nonneg _)
      ((LocalGeometricFontaine.mem_integerRing Ψ _).mp y.property)))⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e (x : Ω) (y : Ω))
  map_add' x y := Subtype.ext (map_add e (x : Ω) (y : Ω))

@[simp] theorem integerEquiv_apply (x : LocalGeometricFontaine.integerRing Ω) :
    (integerEquiv e d hd hnorm x : Ψ) = e x := rfl

@[simp] theorem integerEquiv_symm_apply (y : LocalGeometricFontaine.integerRing Ψ) :
    ((integerEquiv e d hd hnorm).symm y : Ω) = e.symm y := rfl

variable (p : ℕ)

def modPEquiv : ModP (LocalGeometricFontaine.integerRing Ω) p ≃+*
    ModP (LocalGeometricFontaine.integerRing Ψ) p :=
  Ideal.quotientEquiv
    (Ideal.span {(p : LocalGeometricFontaine.integerRing Ω)})
    (Ideal.span {(p : LocalGeometricFontaine.integerRing Ψ)})
    (integerEquiv e d hd hnorm)
    (by simp only [Ideal.map_span, Set.image_singleton, map_natCast])

@[simp] theorem modPEquiv_mk (x : LocalGeometricFontaine.integerRing Ω) :
    modPEquiv e d hd hnorm p
        (Ideal.Quotient.mk (Ideal.span {(p : LocalGeometricFontaine.integerRing Ω)}) x) =
      Ideal.Quotient.mk (Ideal.span {(p : LocalGeometricFontaine.integerRing Ψ)})
        (integerEquiv e d hd hnorm x) := rfl

variable [Fact p.Prime]
variable [Fact (0 < ‖(p : Ω)‖ ∧ ‖(p : Ω)‖ < 1)]
variable [Fact (0 < ‖(p : Ψ)‖ ∧ ‖(p : Ψ)‖ < 1)]

def preTiltEquiv : GeometricTiltField.Source Ω p ≃+* GeometricTiltField.Source Ψ p where
  __ := Perfection.map p (modPEquiv e d hd hnorm p).toRingHom
  invFun := Perfection.map p (modPEquiv e d hd hnorm p).symm.toRingHom
  left_inv x := by
    apply Perfection.ext
    intro n
    change (modPEquiv e d hd hnorm p).symm
      (modPEquiv e d hd hnorm p (Perfection.coeff _ p n x)) = _
    exact (modPEquiv e d hd hnorm p).symm_apply_apply _
  right_inv y := by
    apply Perfection.ext
    intro n
    change modPEquiv e d hd hnorm p
      ((modPEquiv e d hd hnorm p).symm (Perfection.coeff _ p n y)) = _
    exact (modPEquiv e d hd hnorm p).apply_symm_apply _

@[simp] theorem preTiltEquiv_coeff (x : GeometricTiltField.Source Ω p) (n : ℕ) :
    PreTilt.coeff n (preTiltEquiv e d hd hnorm p x) =
      modPEquiv e d hd hnorm p (PreTilt.coeff n x) := rfl

@[simp] theorem preTiltEquiv_symm_coeff (y : GeometricTiltField.Source Ψ p) (n : ℕ) :
    PreTilt.coeff n ((preTiltEquiv e d hd hnorm p).symm y) =
      (modPEquiv e d hd hnorm p).symm (PreTilt.coeff n y) := rfl

theorem modP_preVal_pow (x : ModP (LocalGeometricFontaine.integerRing Ω) p) :
    ModP.preVal Ψ (NormedField.valuation (K := Ψ))
        (LocalGeometricFontaine.integerRing Ψ) p (modPEquiv e d hd hnorm p x) ^ d =
      ModP.preVal Ω (NormedField.valuation (K := Ω))
        (LocalGeometricFontaine.integerRing Ω) p x := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, ModP.preVal_zero, zero_pow hd.ne']
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have he : (Ideal.Quotient.mk (Ideal.span {(p : LocalGeometricFontaine.integerRing Ψ)})
      (integerEquiv e d hd hnorm a) : ModP (LocalGeometricFontaine.integerRing Ψ) p) ≠ 0 := by
    rw [← modPEquiv_mk e d hd hnorm p]
    simpa only [map_zero] using (modPEquiv e d hd hnorm p).injective.ne hx
  rw [modPEquiv_mk,
    ModP.preVal_mk (Valuation.integer.integers _) he,
    ModP.preVal_mk (Valuation.integer.integers _) hx]
  apply Subtype.ext
  change ‖e (a : Ω)‖ ^ d = ‖(a : Ω)‖
  exact hnorm a

theorem sourceValuation_pow (x : GeometricTiltField.Source Ω p) :
    GeometricTiltField.sourceValuation Ψ p (preTiltEquiv e d hd hnorm p x) ^ d =
      GeometricTiltField.sourceValuation Ω p x := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, zero_pow hd.ne']
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n x ≠ 0 := by
    by_contra h
    apply hx
    apply Perfection.ext
    intro n
    have hz : PreTilt.coeff n x = 0 := by
      by_contra hn
      exact h ⟨n, hn⟩
    exact hz.trans (map_zero _).symm
  have he : PreTilt.coeff n (preTiltEquiv e d hd hnorm p x) ≠ 0 := by
    rw [preTiltEquiv_coeff]
    simpa only [map_zero] using (modPEquiv e d hd hnorm p).injective.ne hn
  change PreTilt.valAux Ψ (NormedField.valuation (K := Ψ))
      (LocalGeometricFontaine.integerRing Ψ) p (preTiltEquiv e d hd hnorm p x) ^ d =
    PreTilt.valAux Ω (NormedField.valuation (K := Ω))
      (LocalGeometricFontaine.integerRing Ω) p x
  rw [PreTilt.valAux_eq (Valuation.integer.integers _) he,
    PreTilt.valAux_eq (Valuation.integer.integers _) hn, preTiltEquiv_coeff]
  calc
    _ = (ModP.preVal Ψ (NormedField.valuation (K := Ψ))
        (LocalGeometricFontaine.integerRing Ψ) p
        (modPEquiv e d hd hnorm p (PreTilt.coeff n x)) ^ d) ^ p ^ n := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = _ := by rw [modP_preVal_pow e d hd hnorm p]

def fractionEquiv : GeometricTiltField.FractionField Ω p ≃+*
    GeometricTiltField.FractionField Ψ p :=
  IsFractionRing.ringEquivOfRingEquiv (preTiltEquiv e d hd hnorm p)

@[simp] theorem fractionEquiv_inclusion (x : GeometricTiltField.Source Ω p) :
    fractionEquiv e d hd hnorm p
        (algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p) x) =
      algebraMap (GeometricTiltField.Source Ψ p) (GeometricTiltField.FractionField Ψ p)
        (preTiltEquiv e d hd hnorm p x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (preTiltEquiv e d hd hnorm p) x

theorem fractionEquiv_div (a b : GeometricTiltField.Source Ω p) :
    fractionEquiv e d hd hnorm p
        (algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p) a /
          algebraMap (GeometricTiltField.Source Ω p) (GeometricTiltField.FractionField Ω p) b) =
      algebraMap (GeometricTiltField.Source Ψ p) (GeometricTiltField.FractionField Ψ p)
          (preTiltEquiv e d hd hnorm p a) /
        algebraMap (GeometricTiltField.Source Ψ p) (GeometricTiltField.FractionField Ψ p)
          (preTiltEquiv e d hd hnorm p b) := by
  rw [map_div₀, fractionEquiv_inclusion, fractionEquiv_inclusion]

theorem fractionValuation_pow (x : GeometricTiltField.FractionField Ω p) :
    GeometricTiltField.fractionValuation Ψ p (fractionEquiv e d hd hnorm p x) ^ d =
      GeometricTiltField.fractionValuation Ω p x := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (GeometricTiltField.Source Ω p) x
  rw [fractionEquiv_div, GeometricTiltField.fractionValuation_div,
    GeometricTiltField.fractionValuation_div, div_pow,
    sourceValuation_pow, sourceValuation_pow]

end
end JoshiTeich.Act1Scene1.GeometricTiltComparison
