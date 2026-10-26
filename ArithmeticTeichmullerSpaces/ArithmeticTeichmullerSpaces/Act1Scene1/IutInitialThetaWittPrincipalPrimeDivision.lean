import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalUnitInjective

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-PRINCIPAL-PRIME-DIVISION
source: Joshi II `eq:tate-module-of-lubin-tate` and the multiplicative
formal-group description used in `pr:teichmuller-lift-A`.
fidelity: restricts the actual inverse iterated tilt Frobenius to principal
units. Proves the p-power root law and uniqueness on the original group.
The existing period logarithm sends this root to the actual inverse
p-power scalar multiple, also in its existing phi=p codomain.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; this supplies actual p-division, without assuming
a scalar action on all principal units or full period representation.
Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittPrincipalPrimeDivision

open JoshiTeich.Prologue InitialThetaWittPrincipalUnitDomain
open InitialThetaWittPrincipalUnitPeriod InitialThetaWittPrincipalUnitInjective
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem inverseFrobenius_near_one (k : ℕ) (u : Principal D w) :
    ‖(iterateFrobeniusEquiv (InitialThetaTiltField.Carrier D w)
      (Arithmetic.residueChar w.1) k).symm ((u : (InitialThetaTiltField.Carrier D w)ˣ) :
        InitialThetaTiltField.Carrier D w) - 1‖ < 1 := by
  let e := iterateFrobeniusEquiv (InitialThetaTiltField.Carrier D w) (Arithmetic.residueChar w.1) k
  have he : (e.symm ((u : (InitialThetaTiltField.Carrier D w)ˣ) :
      InitialThetaTiltField.Carrier D w) - 1) ^ (Arithmetic.residueChar w.1 ^ k) =
      ((u : (InitialThetaTiltField.Carrier D w)ˣ) : InitialThetaTiltField.Carrier D w) - 1 := by
    change e (e.symm _ - 1) = _
    rw [map_sub, map_one, RingEquiv.apply_symm_apply]
  apply (pow_lt_one_iff_of_nonneg (norm_nonneg _)
    (pow_ne_zero k (Arithmetic.residueChar_prime w.1).ne_zero)).mp
  rw [← norm_pow, he]
  exact u.property

def primeRoot (k : ℕ) : Principal D w →* Principal D w where
  toFun u := ⟨Units.map (iterateFrobeniusEquiv (InitialThetaTiltField.Carrier D w)
    (Arithmetic.residueChar w.1) k).symm.toMonoidHom u.val, inverseFrobenius_near_one D w k u⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.val v.val)

theorem primeRoot_pow (k : ℕ) (u : Principal D w) :
    primeRoot D w k u ^ (Arithmetic.residueChar w.1 ^ k) = u := by
  apply Subtype.ext
  apply Units.ext
  exact (iterateFrobeniusEquiv (InitialThetaTiltField.Carrier D w)
    (Arithmetic.residueChar w.1) k).apply_symm_apply _

theorem primeRoot_unique (k : ℕ) (u v : Principal D w)
    (hv : v ^ (Arithmetic.residueChar w.1 ^ k) = u) : v = primeRoot D w k u := by
  apply Subtype.ext
  apply Units.ext
  apply (iterateFrobeniusEquiv (InitialThetaTiltField.Carrier D w)
    (Arithmetic.residueChar w.1) k).injective
  exact congrArg (fun z : Principal D w =>
    ((z : (InitialThetaTiltField.Carrier D w)ˣ) : InitialThetaTiltField.Carrier D w))
      (hv.trans (primeRoot_pow D w k u).symm)

theorem periodLog_primeRoot (k : ℕ) (u : Principal D w) :
    periodLog D w (primeRoot D w k u) =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k)⁻¹ • periodLog D w u := by
  have he := congrArg (periodLog D w) (primeRoot_pow D w k u)
  rw [periodLog_pow] at he
  have hs : ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k) •
      periodLog D w (primeRoot D w k u) = periodLog D w u := by
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using he
  have hp : (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k ≠ 0 :=
    pow_ne_zero k (Nat.cast_ne_zero.mpr (Arithmetic.residueChar_prime w.1).ne_zero)
  rw [← hs, inv_smul_smul₀ hp]

theorem eigenLogHom_primeRoot (k : ℕ) (u : Principal D w) :
    eigenLogHom D w (Additive.ofMul (primeRoot D w k u)) =
      ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k)⁻¹ •
        eigenLogHom D w (Additive.ofMul u) := by
  apply Subtype.ext
  rw [Submodule.coe_smul]
  change periodLog D w (Additive.ofMul (primeRoot D w k u)).toMul =
    ((Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) ^ k)⁻¹ •
      periodLog D w (Additive.ofMul u).toMul
  simpa only [toMul_ofMul] using periodLog_primeRoot D w k u

end
end JoshiTeich.Act1Scene1.InitialThetaWittPrincipalPrimeDivision
