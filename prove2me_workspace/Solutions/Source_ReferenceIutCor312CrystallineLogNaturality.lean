import Solutions.Source_ReferenceIutCor312CrystallineMaps

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "θ" => (Perfectoid.thetaMap (O := LocalGeometricFontaine.integerRing C) (p := p))
local notation "I" => (Ideal.span {(p : A0 C p)} : Ideal (A0 C p))

private theorem mapA0_logPartialSum (f : Ainf C p →+* Ainf C p)
    (hf : ∀ x ∈ RingHom.ker θ, f x ∈ kerSupPrime C p)
    (x : Ainf C p) (hx : x ∈ kerSupPrime C p) (hfx : f x ∈ kerSupPrime C p) (N : ℕ) :
    mapA0 C p f hf (DividedPowerLog.logPartialSum
      (fun n => gammaInOfMemKerSupPrime C p n x hx) N) =
    DividedPowerLog.logPartialSum (fun n => gammaInOfMemKerSupPrime C p n (f x) hfx) N := by
  unfold DividedPowerLog.logPartialSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [DividedPowerLog.logTerm, map_mul, map_pow, map_neg, map_one, map_natCast,
    mapA0_gammaInOfMemKerSupPrime C p f hf _ x hx hfx]

theorem mapACris_logOfMemKerSupPrime (f : Ainf C p →+* Ainf C p)
    (hf : ∀ x ∈ RingHom.ker θ, f x ∈ kerSupPrime C p)
    {x y : Ainf C p} (hx : x ∈ kerSupPrime C p) (hy : y ∈ kerSupPrime C p)
    (hxy : f x = y) :
    mapACris C p (mapA0 C p f hf) (logOfMemKerSupPrime C p x hx) =
      logOfMemKerSupPrime C p y hy := by
  subst y
  apply AdicCompletion.ext_evalₐ
  intro k
  let N := p * k
  let γ : ℕ → A0 C p := fun n => gammaInOfMemKerSupPrime C p n x hx
  let γ' : ℕ → A0 C p := fun n => gammaInOfMemKerSupPrime C p n (f x) hy
  have hxk := eval_logOfMemKerSupPrime C p x hx (k := k) (N := N) le_rfl
  have hyk := eval_logOfMemKerSupPrime C p (f x) hy (k := k) (N := N) le_rfl
  calc
    _ = Ideal.Quotient.mk (I ^ k) (mapA0 C p f hf (DividedPowerLog.logPartialSum γ N)) :=
      eval_mapACris_of_eq C p (mapA0 C p f hf) k _ _ hxk
    _ = Ideal.Quotient.mk (I ^ k) (DividedPowerLog.logPartialSum γ' N) :=
      congrArg (Ideal.Quotient.mk (I ^ k)) (mapA0_logPartialSum C p f hf x hx hy N)
    _ = _ := hyk.symm

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
