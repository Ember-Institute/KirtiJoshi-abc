import Mathlib.Logic.Function.Defs

/-!
source-id: JT-SCENE1-FROBENIUS-FUNCTION-TRANSFER
source: Joshi II `se:ff-rings`, functorial Frobenius comparison;
substitution along equality of functions.
fidelity: transfers a proved Frobenius commutation law along equalities
of the two Frobenius functions or the comparison function. Naturality is
the first argument, so its functions can be inferred from the original
proof. No ring instances, bundled maps, or additional source laws are used.
Original proofs; no reference implementation copied.
boundary: generic function substitution only; each concrete consumer must
supply its proved function identities and naturality law.
-/

namespace JoshiTeich.Act1Scene1.FrobeniusFunctionTransfer

theorem transfer {A B : Type*} {E : A → B}
    {F₀ F₁ : A → A} {G₀ G₁ : B → B}
    (hnat : ∀ x, E (F₀ x) = G₀ (E x))
    (hF : F₁ = F₀) (hG : G₀ = G₁) (x : A) :
    E (F₁ x) = G₁ (E x) := by
  cases hF
  cases hG
  exact hnat x

theorem transfer_map {A B : Type*} {E₀ E₁ : A → B}
    {F : A → A} {G : B → B}
    (hnat : ∀ x, E₀ (F x) = G (E₀ x))
    (hE : E₀ = E₁) (x : A) :
    E₁ (F x) = G (E₁ x) := by
  cases hE
  exact hnat x

end JoshiTeich.Act1Scene1.FrobeniusFunctionTransfer
