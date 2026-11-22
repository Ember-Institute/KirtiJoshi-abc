import Solutions.Source_ReferenceIutCor312CrystallineACrisComparison
import Solutions.Source_ReferenceIutCor312KummerCrystallineBridge

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open GeometricTiltComparison

noncomputable section

variable {C C' : Type*} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable [NormedField C'] [IsUltrametricDist C'] [CompleteSpace C']
variable (p : ℕ) [Fact p.Prime]
variable [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable [Fact (0 < ‖(p : C')‖ ∧ ‖(p : C')‖ < 1)]
variable (e : C ≃+* C') (d : ℕ) (hd : 0 < d) (hnorm : ∀ x : C, ‖e x‖ ^ d = ‖x‖)

local notation "𝓌" => WittRingEquiv.mapEquiv p (preTiltEquiv e d hd hnorm p)
local notation "I" => (Ideal.span {(p : A0 C p)} : Ideal (A0 C p))
local notation "I'" => (Ideal.span {(p : A0 C' p)} : Ideal (A0 C' p))

/-- The Witt comparison sends logarithm inputs into the target logarithm ideal. -/
theorem mapEquiv_mem_kerSupPrime {x : Ainf C p} (hx : x ∈ kerSupPrime C p) :
    𝓌 x ∈ kerSupPrime C' p := by
  unfold kerSupPrime at hx ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  refine Submodule.mem_sup.mpr
    ⟨_, (mapEquiv_mem_thetaKernel_iff e d hd hnorm p a).mpr ha, _, ?_, rfl⟩
  rw [Ideal.mem_span_singleton] at hb ⊢
  simpa only [map_natCast] using map_dvd (𝓌) hb

theorem equivA0_gammaInOfMemKerSupPrime (n : ℕ) (x : Ainf C p)
    (hx : x ∈ kerSupPrime C p) (hwx : 𝓌 x ∈ kerSupPrime C' p) :
    equivA0 p e d hd hnorm (gammaInOfMemKerSupPrime C p n x hx) =
      gammaInOfMemKerSupPrime C' p n (𝓌 x) hwx := by
  apply Subtype.ext
  rw [equivA0_coe]
  exact invertPrimeEquiv_gamma p e d hd hnorm n x

private theorem equivA0_logPartialSum (x : Ainf C p)
    (hx : x ∈ kerSupPrime C p) (hwx : 𝓌 x ∈ kerSupPrime C' p) (N : ℕ) :
    equivA0 p e d hd hnorm (DividedPowerLog.logPartialSum
      (fun n => gammaInOfMemKerSupPrime C p n x hx) N) =
    DividedPowerLog.logPartialSum
      (fun n => gammaInOfMemKerSupPrime C' p n (𝓌 x) hwx) N := by
  unfold DividedPowerLog.logPartialSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [DividedPowerLog.logTerm, map_mul, map_pow, map_neg, map_one, map_natCast,
    equivA0_gammaInOfMemKerSupPrime p e d hd hnorm _ x hx hwx]

/-- The completed comparison sends the source logarithm to the target
logarithm of the transported Witt input. -/
theorem equivACris_logOfMemKerSupPrime {x : Ainf C p} {y : Ainf C' p}
    (hx : x ∈ kerSupPrime C p) (hy : y ∈ kerSupPrime C' p) (hxy : 𝓌 x = y) :
    equivACris p e d hd hnorm (logOfMemKerSupPrime C p x hx) =
      logOfMemKerSupPrime C' p y hy := by
  subst y
  apply AdicCompletion.ext_evalₐ
  intro k
  let N := p * k
  let γ : ℕ → A0 C p := fun n => gammaInOfMemKerSupPrime C p n x hx
  let γ' : ℕ → A0 C' p := fun n => gammaInOfMemKerSupPrime C' p n (𝓌 x) hy
  have hxk := eval_logOfMemKerSupPrime C p x hx (k := k) (N := N) le_rfl
  have hyk := eval_logOfMemKerSupPrime C' p (𝓌 x) hy (k := k) (N := N) le_rfl
  calc
    _ = Ideal.Quotient.mk (I' ^ k)
        (equivA0 p e d hd hnorm (DividedPowerLog.logPartialSum γ N)) :=
      eval_equivACris_of_eq p e d hd hnorm k _ _ hxk
    _ = Ideal.Quotient.mk (I' ^ k) (DividedPowerLog.logPartialSum γ' N) :=
      congrArg (Ideal.Quotient.mk (I' ^ k)) (equivA0_logPartialSum p e d hd hnorm x hx hy N)
    _ = _ := hyk.symm

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
