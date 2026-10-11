/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/Existence.lean`
original-commit: `a36b42b9a221e1baaf434bb76c85b3a0dfbf33a7`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: adapts the `VBadOf`/`badPlacesOver_VBadOf` support filter to
the local `InitialThetaData` support; derives the exclusion and obstruction
from its actual admissible-prime fields. No reference-project import is used.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaBadSupport

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField

universe u

/-!
source-id: IUT-COR312-INITIAL-THETA-PRIME-TO-SUPPORT
source: `refer/iut/Iut/Concrete/Existence.lean`, `VBadOf` and
`badPlacesOver_VBadOf`; `AdmissiblePrimeData.residueChar_coprime`.
fidelity: the actual q-pilot carrier excludes residue characteristic ell.
The reference construction's maximal locus is the odd multiplicative support
with the ell fibre removed. Identifying a supplied VBad with that locus stays
explicit. Equality with the unfiltered support additionally requires absence
of multiplicative reduction above ell.
boundary: Scene1/Derived
-/

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

/-- The admissible prime excludes its own residue characteristic from VBad. -/
theorem iutInitialThetaVBad_residueChar_ne_ell
    {v : NumberField.FinitePlace (JoshiTeich.ReferenceIut.fieldOfModuli D.F D.E)}
    (hv : v ∈ D.VBad) : Arithmetic.residueChar v ≠ D.prime.ℓ := by
  exact ((Nat.coprime_primes D.prime.ℓ_prime
    (Arithmetic.residueChar_prime v)).mp (D.prime.residueChar_coprime v hv)).symm

/-- Every actual q-pilot base place has residue characteristic different from ell. -/
theorem iutInitialThetaBadPlacesOver_residueChar_ne_ell
    {w : NumberField.FinitePlace D.F}
    (hw : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad) :
    Arithmetic.residueChar w ≠ D.prime.ℓ := by
  obtain ⟨v, hv, hwv⟩ := hw
  rw [Arithmetic.residueChar_eq_of_liesOver hwv]
  exact iutInitialThetaVBad_residueChar_ne_ell D hv

/-- The unconditional inclusion retains the admissible-prime filter. -/
theorem iutInitialThetaBadPlacesOver_subset_primeToOddSupport :
    JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad ⊆
      {w | w ∈ IutOddMultiplicativeSupport D ∧
        Arithmetic.residueChar w ≠ D.prime.ℓ} := by
  intro w hw
  exact ⟨iutBadPlacesOver_subset_oddMultiplicativeSupport D hw,
    iutInitialThetaBadPlacesOver_residueChar_ne_ell D hw⟩

/-- A multiplicative place above ell prevents equality with the full odd support. -/
theorem iutInitialThetaOddMultiplicativeSupport_ne_badPlacesOver_of_multiplicative_at_ell
    {w : NumberField.FinitePlace D.F}
    (hw : JoshiTeich.ReferenceIut.HasMultiplicativeReductionAt D.E w)
    (hChar : Arithmetic.residueChar w = D.prime.ℓ) :
    IutOddMultiplicativeSupport D ≠
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := by
  intro hEq
  have hOdd : Odd D.prime.ℓ :=
    D.prime.ℓ_prime.odd_of_ne_two (by have := D.prime.five_le; omega)
  have hFull : w ∈ IutOddMultiplicativeSupport D := ⟨by rwa [hChar], hw⟩
  have hBad : w ∈ JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad :=
    hEq ▸ hFull
  exact iutInitialThetaBadPlacesOver_residueChar_ne_ell D hBad hChar

/-- Pullback commutes with removal of the ell residue-characteristic fibre.
This is the local adaptation of the reference `badPlacesOver_VBadOf` identity. -/
theorem iutInitialThetaBadPlacesOver_primeToOddModSupport_eq :
    JoshiTeich.ReferenceIut.badPlacesOver D.F D.E
        {v | v ∈ IutOddMultiplicativeModSupport D ∧
          Arithmetic.residueChar v ≠ D.prime.ℓ} =
      {w | w ∈ IutOddMultiplicativeSupport D ∧
        Arithmetic.residueChar w ≠ D.prime.ℓ} := by
  ext w
  constructor
  · rintro ⟨v, ⟨hv, hChar⟩, hwv⟩
    have hFull : w ∈ IutOddMultiplicativeSupport D := by
      rw [iutOddMultiplicativeSupport_eq_badPlacesOver_modSupport D]
      exact ⟨v, hv, hwv⟩
    refine ⟨hFull, ?_⟩
    rwa [Arithmetic.residueChar_eq_of_liesOver hwv]
  · rintro ⟨hFull, hChar⟩
    rw [iutOddMultiplicativeSupport_eq_badPlacesOver_modSupport D] at hFull
    obtain ⟨v, hv, hwv⟩ := hFull
    exact ⟨v, ⟨hv, (Arithmetic.residueChar_eq_of_liesOver hwv) ▸ hChar⟩, hwv⟩

/-- A VBad chosen as in the reference construction yields the filtered support. -/
theorem iutInitialThetaBadPlacesOver_eq_primeToOddSupport_of_VBad_eq
    (hVBad : D.VBad = {v | v ∈ IutOddMultiplicativeModSupport D ∧
      Arithmetic.residueChar v ≠ D.prime.ℓ}) :
    JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad =
      {w | w ∈ IutOddMultiplicativeSupport D ∧
        Arithmetic.residueChar w ≠ D.prime.ℓ} := by
  exact (congrArg (JoshiTeich.ReferenceIut.badPlacesOver D.F D.E) hVBad).trans
    (iutInitialThetaBadPlacesOver_primeToOddModSupport_eq D)

/-- For the maximal prime-to-ell choice, S1.199 coverage holds exactly when
there is no multiplicative place above ell. -/
theorem iutInitialThetaOddMultiplicativeSupport_eq_badPlacesOver_iff_no_multiplicative_at_ell
    (hVBad : D.VBad = {v | v ∈ IutOddMultiplicativeModSupport D ∧
      Arithmetic.residueChar v ≠ D.prime.ℓ}) :
    IutOddMultiplicativeSupport D =
        JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad ↔
      ∀ w : NumberField.FinitePlace D.F, Arithmetic.residueChar w = D.prime.ℓ →
        ¬ JoshiTeich.ReferenceIut.HasMultiplicativeReductionAt D.E w := by
  constructor
  · intro hEq w hChar hw
    exact
      iutInitialThetaOddMultiplicativeSupport_ne_badPlacesOver_of_multiplicative_at_ell
        D hw hChar hEq
  · intro hNoMult
    rw [iutInitialThetaBadPlacesOver_eq_primeToOddSupport_of_VBad_eq D hVBad]
    ext w
    constructor
    · intro hw
      exact ⟨hw, fun hChar => hNoMult w hChar hw.2⟩
    · exact And.left

end JoshiTeich.Act1Scene1
