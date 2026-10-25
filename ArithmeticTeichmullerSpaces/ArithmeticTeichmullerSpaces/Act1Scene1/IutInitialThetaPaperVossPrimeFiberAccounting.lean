import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperVossPrimeFiberMultiplicity

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

/-!
source-id: JT-SCENE1-PAPER-VOSS-PRIME-FIBER-ACCOUNTING
source: Joshi III, the prime-indexed odd semistable carrier
underline V odd,ss_p and its finite prime support.
fidelity: packages the concrete section/Voss carrier as the Sigma of its
residue-characteristic fibers and derives the exact finite cardinality sum.
The same decomposition is applied to the actual VBad representative image.
boundary: this is concrete carrier accounting.  It does not identify the
carrier with the paper's L' representatives, multiplicities, omitted mass,
or mixed-moduli descent.
-/

/-- The finite type of rational residue characteristics occurring in the carrier. -/
abbrev iutInitialThetaSectionVossPrimeSupportType :=
  {p : ℕ // p ∈ iutInitialThetaSectionVossPrimeSupport D}

noncomputable instance iutInitialThetaSectionVossPrimeSupportTypeFintype :
    Fintype (iutInitialThetaSectionVossPrimeSupportType D) :=
  (iutInitialThetaSectionVossPrimeSupport_finite D).fintype

noncomputable instance iutInitialThetaSectionVossFintype :
    Fintype {w : NumberField.FinitePlace ↥D.prime.torsionField //
      w ∈ iutInitialThetaSectionVoss D} :=
  (iutInitialThetaSectionVoss_finite D).fintype

/-- The concrete carrier is equivalent to the Sigma of its prime fibers. -/
noncomputable def iutInitialThetaSectionVossPrimeFiberSigmaEquiv :
    {w : NumberField.FinitePlace ↥D.prime.torsionField //
        w ∈ iutInitialThetaSectionVoss D} ≃
      Σ p : iutInitialThetaSectionVossPrimeSupportType D,
        iutInitialThetaSectionVossPrimeFiber D p.1 := by
  classical
  refine Equiv.ofBijective
    (fun w =>
      ⟨⟨Arithmetic.residueChar w.1,
        ⟨w.1, w.2, rfl⟩⟩,
        ⟨w.1, ⟨w.2, rfl⟩⟩⟩) ?_
  constructor
  · intro w₁ w₂ h
    apply Subtype.ext
    exact congrArg (fun x => x.2.1) h
  · rintro ⟨⟨p, hpSupport⟩, ⟨place, hplaceVoss, hp⟩⟩
    change Arithmetic.residueChar place = p at hp
    subst p
    refine ⟨⟨place, hplaceVoss⟩, ?_⟩
    rfl

theorem iutInitialThetaSectionVoss_card_eq_primeFiber_sum :
    Fintype.card
        {w : NumberField.FinitePlace ↥D.prime.torsionField //
          w ∈ iutInitialThetaSectionVoss D} =
      ∑ p : iutInitialThetaSectionVossPrimeSupportType D,
        iutInitialThetaSectionVossPrimeMultiplicity D p.1 := by
  rw [Fintype.card_congr (iutInitialThetaSectionVossPrimeFiberSigmaEquiv D),
    Fintype.card_sigma]
  rfl

end
end JoshiTeich.Act1Scene1
