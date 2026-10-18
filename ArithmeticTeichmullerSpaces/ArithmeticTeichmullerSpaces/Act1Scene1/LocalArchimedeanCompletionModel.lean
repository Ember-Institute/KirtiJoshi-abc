import ArithmeticTeichmullerSpaces.Act1Scene1.LocalArchimedeanTensor
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
source-id: JT-SCENE1-LOCAL-ARCHIMEDEAN-COMPLETION-MODEL
source: Mathlib `NumberField.InfinitePlace.Completion.extensionEmbedding`,
its real/complex surjectivity and isometry theorems; reference
`LocalConstruct/Packet.lean` models an infinite completion as R or C.
fidelity: identifies the chosen real/complex factor model with the actual
infinite completion by a norm-preserving ring equivalence. The forward
map is the canonical extension of the place embedding, not an arbitrary
isomorphism. Original proofs; no reference code copied.
boundary: Scene1/Derived; no new Core contracts.
-/

namespace JoshiTeich.Act1Scene1.LocalArchimedean

open NumberField
universe u
noncomputable section
variable {K : Type u} [Field K] (w : InfinitePlace K)

private theorem extensionEmbedding_mem_archField (x : w.Completion) :
    InfinitePlace.Completion.extensionEmbedding w x ∈ archField w := by
  by_cases hw : w.IsReal
  · rw [archField_of_isReal hw]
    apply Algebra.mem_bot.mpr
    exact ⟨InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x⟩
  · rw [archField_of_isComplex (InfinitePlace.not_isReal_iff_isComplex.mp hw)]
    exact Algebra.mem_top

def completionModelHom : w.Completion →+* Factor w where
  toFun x := ⟨⟨InfinitePlace.Completion.extensionEmbedding w x,
    extensionEmbedding_mem_archField w x⟩⟩
  map_one' := by apply ULift.ext; apply Subtype.ext; exact map_one _
  map_zero' := by apply ULift.ext; apply Subtype.ext; exact map_zero _
  map_add' x y := by apply ULift.ext; apply Subtype.ext; exact map_add _ x y
  map_mul' x y := by apply ULift.ext; apply Subtype.ext; exact map_mul _ x y

theorem completionModelHom_complex (x : w.Completion) :
    ((completionModelHom w x).down : ℂ) =
      InfinitePlace.Completion.extensionEmbedding w x := rfl

theorem completionModelHom_bijective : Function.Bijective (completionModelHom w) := by
  constructor
  · intro x y h
    apply (InfinitePlace.Completion.extensionEmbedding w).injective
    exact congrArg (fun z : Factor w => (z.down : ℂ)) h
  · intro y
    by_cases hw : w.IsReal
    · have hy : (y.down : ℂ) ∈ (⊥ : Subalgebra ℝ ℂ) :=
        archField_of_isReal hw ▸ y.down.2
      obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hy
      obtain ⟨x, hx⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw r
      refine ⟨x, ?_⟩
      apply ULift.ext
      apply Subtype.ext
      change InfinitePlace.Completion.extensionEmbedding w x = (y.down : ℂ)
      rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, hx]
      exact hr
    · obtain ⟨x, hx⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp hw) (y.down : ℂ)
      refine ⟨x, ?_⟩
      apply ULift.ext
      exact Subtype.ext hx

def completionModelEquiv : w.Completion ≃+* Factor w :=
  RingEquiv.ofBijective (completionModelHom w) (completionModelHom_bijective w)

def completionNormedEquiv : w.Completion ≃ NormedFactor w where
  toFun x := ⟨(completionModelEquiv w x).down⟩
  invFun y := (completionModelEquiv w).symm ⟨y.down⟩
  left_inv x := (completionModelEquiv w).symm_apply_apply x
  right_inv y := by
    change (completionModelEquiv w) ((completionModelEquiv w).symm y) = y
    exact (completionModelEquiv w).apply_symm_apply y

theorem completionModelEquiv_norm (x : w.Completion) :
    ‖completionNormedEquiv w x‖ = ‖x‖ := by
  change ‖InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
    (map_zero _) x

def completionModelIsometry : w.Completion ≃ᵢ NormedFactor w where
  toEquiv := completionNormedEquiv w
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    change dist (InfinitePlace.Completion.extensionEmbedding w x)
      (InfinitePlace.Completion.extensionEmbedding w y) = dist x y
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq x y

end
end JoshiTeich.Act1Scene1.LocalArchimedean
