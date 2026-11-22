import ArithmeticTeichmullerSpaces.Act1Scene1.CyclotomicTateTilt

/-!
The Kummer tower for the standard-point comparison in Joshi III (9.9.4)–(9.9.6)
gives compatible roots in the valuation ring. Reducing those roots modulo the
residue prime gives the pretilt input of the Fontaine map.
-/

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.LocalKummer.RootTower
open JoshiTeich.Prologue
universe u v w
noncomputable section

variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
variable {C : Type w} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable {p : ℕ} [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable {a : K} (R : RootTower (Ω := Ω) p a) (j : Ω →+* C)
variable (ha : ‖j (algebraMap K Ω a)‖ ≤ 1)

local notation "𝒪" => LocalGeometricFontaine.integerRing C

/-- An algebraic root of the original tower in the valuation integers. -/
def integralCoordinate (n : ℕ) : 𝒪 :=
  ⟨j (R.root n), (LocalGeometricFontaine.mem_integerRing C _).mpr (by
    have hpow : ‖j (R.root n)‖ ^ (p ^ n) ≤ 1 := by
      rw [← norm_pow, ← map_pow, R.root_pow_eq]
      exact ha
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _)
      (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp hpow)⟩

private def baseCoordinate : 𝒪 :=
  ⟨j (algebraMap K Ω a), (LocalGeometricFontaine.mem_integerRing C _).mpr ha⟩

omit [CompleteSpace C] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)] in
private theorem integralCoordinate_succ (n : ℕ) :
    integralCoordinate R j ha (n + 1) ^ p = integralCoordinate R j ha n := by
  apply Subtype.ext
  change j (R.root (n + 1)) ^ p = j (R.root n)
  rw [← map_pow, R.root_succ]

omit [CompleteSpace C] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)] in
private theorem integralCoordinate_pow (n : ℕ) :
    integralCoordinate R j ha n ^ (p ^ n) = baseCoordinate j ha := by
  apply Subtype.ext
  change j (R.root n) ^ (p ^ n) = j (algebraMap K Ω a)
  rw [← map_pow, R.root_pow_eq]

-- The coordinates come from the same root tower as the Kummer cocycle.
def toGeometricPreTilt : GeometricTiltField.Source C p :=
  ⟨fun n => Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) (integralCoordinate R j ha n),
    fun n => by
      rw [← map_pow]
      exact congrArg (Ideal.Quotient.mk _) (integralCoordinate_succ R j ha n)⟩

private theorem untilt_eq_baseCoordinate :
    PreTilt.untilt (toGeometricPreTilt R j ha) = baseCoordinate j ha := by
  change Perfection.teichmuller p (Ideal.span {(p : 𝒪)})
    (toGeometricPreTilt R j ha) = baseCoordinate j ha
  apply Perfection.teichmuller_spec
  intro n
  refine ⟨integralCoordinate R j ha n, rfl, ?_⟩
  simp only [integralCoordinate_pow, SModEq.refl]

theorem theta_teichmuller_toGeometricPreTilt :
    (Perfectoid.thetaMap (O := 𝒪) (p := p)
      (WittVector.teichmuller p (toGeometricPreTilt R j ha)) : C) =
      j (algebraMap K Ω a) := by
  rw [Perfectoid.thetaMap_teichmuller]
  exact congrArg Subtype.val (untilt_eq_baseCoordinate R j ha)

end
end JoshiTeich.Act1Scene1.LocalKummer.RootTower
