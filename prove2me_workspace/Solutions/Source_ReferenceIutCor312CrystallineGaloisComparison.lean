import Solutions.Source_ReferenceIutCor312CrystallineA0HomExt
import Solutions.Source_ReferenceIutCor312CrystallineACrisComparison
import Solutions.Source_ReferenceIutCor312CrystallineGalois
import Solutions.Source_ReferenceIutCor312CrystallineGaloisTiltComparison

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CompletedAlgebraicClosure

open CrystallineEnvelope GeometricTiltComparison

noncomputable section

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable {C : Type*} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime]
variable [Fact (0 < ‖(p : Field K)‖ ∧ ‖(p : Field K)‖ < 1)]
variable [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable (e : Field K ≃+* C) (d : ℕ) (hd : 0 < d)
variable (hnorm : ∀ x : Field K, ‖e x‖ ^ d = ‖x‖)
variable (σ : Algebraic K ≃ₐ[K] Algebraic K)
variable (g : C ≃+* C) (hg : ∀ x : C, ‖g x‖ ^ (1 : ℕ) = ‖x‖)
variable (hcomm : ∀ x : Field K, e (extendGalois σ x) = g (e x))

local notation "I" => (Ideal.span {(p : A0 (Field K) p)} : Ideal (A0 (Field K) p))
local notation "J" => (Ideal.span {(p : A0 C p)} : Ideal (A0 C p))

include hcomm

/-- The divided-power comparison intertwines the Galois endomorphisms. -/
theorem equivA0_extendGaloisA0 (x : A0 (Field K) p) :
    equivA0 p e d hd hnorm (extendGaloisA0 p σ x) =
      equivA0 p g 1 Nat.one_pos hg (equivA0 p e d hd hnorm x) := by
  let f := (equivA0 p e d hd hnorm).toRingHom.comp (extendGaloisA0 p σ)
  let f' := (equivA0 p g 1 Nat.one_pos hg).toRingHom.comp (equivA0 p e d hd hnorm).toRingHom
  have heq : f = f' := by
    apply ringHom_ext_of_Ainf p
    intro a
    change equivA0 p e d hd hnorm (extendGaloisA0 p σ
        (algebraMap (Ainf (Field K) p) (A0 (Field K) p) a)) =
      equivA0 p g 1 Nat.one_pos hg (equivA0 p e d hd hnorm
        (algebraMap (Ainf (Field K) p) (A0 (Field K) p) a))
    simp only [extendGaloisA0_algebraMap, equivA0_algebraMap]
    exact congrArg (algebraMap (Ainf C p) (A0 C p))
      (wittEquiv_extendGaloisFontaine p e d hd hnorm σ g hg hcomm a)
  exact DFunLike.congr_fun heq x

/-- The crystalline comparison intertwines the completed Galois endomorphisms. -/
theorem equivACris_extendGaloisACris (z : ACris (Field K) p) :
    equivACris p e d hd hnorm (extendGaloisACris p σ z) =
      equivACris p g 1 Nat.one_pos hg (equivACris p e d hd hnorm z) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n z)
  have hs : AdicCompletion.evalₐ I n (extendGaloisACris p σ z) =
      Ideal.Quotient.mk (I ^ n) (extendGaloisA0 p σ x) :=
    eval_mapACris_of_eq (Field K) p (extendGaloisA0 p σ) n z x hx.symm
  have ht : AdicCompletion.evalₐ J n (equivACris p e d hd hnorm z) =
      Ideal.Quotient.mk (J ^ n) (equivA0 p e d hd hnorm x) :=
    eval_equivACris_of_eq p e d hd hnorm n z x hx.symm
  calc
    _ = Ideal.Quotient.mk (J ^ n) (equivA0 p e d hd hnorm (extendGaloisA0 p σ x)) :=
      eval_equivACris_of_eq p e d hd hnorm n _ _ hs
    _ = Ideal.Quotient.mk (J ^ n) (equivA0 p g 1 Nat.one_pos hg (equivA0 p e d hd hnorm x)) :=
      congrArg (Ideal.Quotient.mk (J ^ n))
        (equivA0_extendGaloisA0 p e d hd hnorm σ g hg hcomm x)
    _ = _ := (eval_equivACris_of_eq p g 1 Nat.one_pos hg n _ _ ht).symm

end

end JoshiTeich.Act1Scene1.CompletedAlgebraicClosure
