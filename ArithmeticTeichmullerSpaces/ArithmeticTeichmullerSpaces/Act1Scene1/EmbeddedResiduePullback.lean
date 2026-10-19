import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
source-id: JT-SCENE1-EMBEDDED-RESIDUE-PULLBACK
source: ring-theoretic pullback of a residue map along an actual field embedding;
Joshi II eta_K and local Teichmuller evaluation (932--958).
fidelity: evaluates precisely those elements whose residue lies in the embedded
field. Surjectivity and the original kernel are proved, not supplied as inputs.
Original proofs, no reference-engine copy; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.EmbeddedResiduePullback

noncomputable section
variable {A E Ω : Type*} [CommRing A] [Field E] [Field Ω]
variable (θ : A →+* Ω) (ι : E →+* Ω)

def source : Subring A := ι.range.comap θ

def rangeEquiv : E ≃+* ι.range :=
  RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun _ _ h => ι.injective (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩

def evaluation : source θ ι →+* E :=
  (rangeEquiv ι).symm.toRingHom.comp
    { toFun := fun x => ⟨θ x, x.property⟩
      map_one' := Subtype.ext (map_one θ)
      map_mul' := fun a b => Subtype.ext (map_mul θ (a : A) (b : A))
      map_zero' := Subtype.ext (map_zero θ)
      map_add' := fun a b => Subtype.ext (map_add θ (a : A) (b : A)) }

theorem embedding_evaluation (x : source θ ι) : ι (evaluation θ ι x) = θ x := by
  change ((rangeEquiv ι) ((rangeEquiv ι).symm ⟨θ x, x.property⟩) : Ω) = θ x
  exact congrArg Subtype.val ((rangeEquiv ι).apply_symm_apply _)

theorem evaluation_eq_iff (x : source θ ι) (z : E) :
    evaluation θ ι x = z ↔ θ x = ι z := by
  rw [← ι.injective.eq_iff, embedding_evaluation]

theorem surjective (hθ : Function.Surjective θ) : Function.Surjective (evaluation θ ι) := by
  intro z
  obtain ⟨a, ha⟩ := hθ (ι z)
  have hm : a ∈ source θ ι := by
    change θ a ∈ ι.range
    exact ⟨z, ha.symm⟩
  exact ⟨⟨a, hm⟩, (evaluation_eq_iff θ ι _ z).mpr ha⟩

theorem kernel : RingHom.ker (evaluation θ ι) = (RingHom.ker θ).comap (source θ ι).subtype := by
  ext x
  change evaluation θ ι x = 0 ↔ θ x = 0
  simpa only [map_zero] using evaluation_eq_iff θ ι x 0

theorem fiber (x y : source θ ι) :
    evaluation θ ι x = evaluation θ ι y ↔ (x : A) - y ∈ RingHom.ker θ := by
  rw [← ι.injective.eq_iff, embedding_evaluation, embedding_evaluation]
  simp only [RingHom.mem_ker, map_sub, sub_eq_zero]

def quotientEquiv (hθ : Function.Surjective θ) :
    (source θ ι ⧸ RingHom.ker (evaluation θ ι)) ≃+* E :=
  (evaluation θ ι).quotientKerEquivOfSurjective (surjective θ ι hθ)

theorem quotientEquiv_mk (hθ : Function.Surjective θ) (x : source θ ι) :
    quotientEquiv θ ι hθ (Ideal.Quotient.mk _ x) = evaluation θ ι x :=
  RingHom.quotientKerEquivOfSurjective_apply_mk
    (f := evaluation θ ι) (surjective θ ι hθ) x

end
end JoshiTeich.Act1Scene1.EmbeddedResiduePullback
