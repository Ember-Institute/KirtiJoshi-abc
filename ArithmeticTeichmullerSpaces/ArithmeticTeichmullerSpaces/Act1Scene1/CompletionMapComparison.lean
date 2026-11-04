import Mathlib.Logic.Function.Defs

/-!
source-id: JT-SCENE1-COMPLETION-MAP-COMPARISON
source: Joshi II `se:ff-rings`, compatibility of the original bounded
inclusions under completion comparison.
fidelity: ordinary function equalities compose a source comparison square
with two embeddings. The concrete consumer supplies every equality from
the original source and completion maps. No algebraic instance is needed.
Original proof; generic mathematics; no period-ring identity is asserted.
-/

namespace JoshiTeich.Act1Scene1.CompletionMapComparison

theorem change_source_map {A B X Y : Type*}
    {a : A → X} {b : B → Y} {e : X → Y} {f g : A → B}
    (he : ∀ x, e (a x) = b (f x)) (hf : ∀ x, f x = g x) :
    ∀ x, e (a x) = b (g x) :=
  fun x => (he x).trans (congrArg b (hf x))

theorem of_inclusion {R S A B X Y : Type*}
    {r : R → A} {s : S → B} {a : A → X} {b : B → Y}
    {ir : R → X} {is : S → Y} {f : A → B} {g : R → S} {e : X → Y}
    (hr : ∀ x, ir x = a (r x)) (hs : ∀ y, is y = b (s y))
    (hf : ∀ x, f (r x) = s (g x)) (he : ∀ x, e (a x) = b (f x)) :
    ∀ x, e (ir x) = is (g x) :=
  fun x => (congrArg e (hr x)).trans
    ((he (r x)).trans ((congrArg b (hf x)).trans (hs (g x)).symm))

theorem change_original_map {R S X Y : Type*}
    {ir : R → X} {is : S → Y} {e : X → Y} {f g : R → S}
    (he : ∀ x, e (ir x) = is (f x)) (hf : ∀ x, g x = f x) :
    ∀ x, e (ir x) = is (g x) :=
  fun x => (he x).trans (congrArg is (hf x).symm)

theorem of_map {R S A B X Y : Type*}
    {r : R → A} {s : S → B} {a : A → X} {b : B → Y}
    {ir : R → X} {is : S → Y} {f : A → B} {g : R → S} {e : X → Y}
    (he : ∀ x, e (a x) = b (f x)) (hf : ∀ x, f (r x) = s (g x))
    (hr : ∀ x, ir x = a (r x)) (hs : ∀ y, is y = b (s y)) :
    ∀ x, e (ir x) = is (g x) :=
  of_inclusion hr hs hf he

end JoshiTeich.Act1Scene1.CompletionMapComparison
