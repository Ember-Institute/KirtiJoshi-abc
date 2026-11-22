import Solutions.Source_ReferenceIutCor312CrystallineEnvelope

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

noncomputable section

variable {C C' : Type*} [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable [NormedField C'] [IsUltrametricDist C'] [CompleteSpace C']
variable (p : ℕ) [Fact p.Prime]
variable [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable [Fact (0 < ‖(p : C')‖ ∧ ‖(p : C')‖ < 1)]

local notation "ι" => algebraMap (Ainf C p) (A0 C p)

/-- Two ring maps of the integral crystalline subalgebra agree if they
agree on the source Witt ring. -/
theorem ringHom_ext_of_Ainf {f g : A0 C p →+* A0 C' p}
    (h : ∀ x : Ainf C p, f (ι x) = g (ι x)) : f = g := by
  apply RingHom.ext
  intro z
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (Submonoid.powers (p : Ainf C p))
    (z : AinfInvertP C p)
  obtain ⟨n, hn⟩ := b.property
  have hclear : z * ι (b : Ainf C p) = ι a := by
    apply Subtype.ext
    change (z : AinfInvertP C p) * algebraMap (Ainf C p) (AinfInvertP C p) (b : Ainf C p) =
      algebraMap (Ainf C p) (AinfInvertP C p) a
    exact hab
  let val := (A0 C' p).val.toRingHom
  let f' := val.comp f
  let g' := val.comp g
  have hagree (x : Ainf C p) : f' (ι x) = g' (ι x) :=
    congrArg val (h x)
  have hunit : IsUnit (g' (ι (b : Ainf C p))) := by
    simpa only [← hn, map_pow, map_natCast] using
      (natCast_isUnit C' p p (Fact.out : p.Prime).ne_zero).pow n
  apply Subtype.ext
  change f' z = g' z
  apply hunit.mul_right_cancel
  calc
    _ = f' (ι a) := by rw [← hagree, ← map_mul, hclear]
    _ = g' (ι a) := hagree a
    _ = _ := by rw [← map_mul, hclear]

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
