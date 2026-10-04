import ArithmeticTeichmullerSpaces.Prologue.Perfectoid.Untilts

namespace JoshiTeich.Prologue.Perfectoid

open PreTilt WittVector

variable {O : Type*} [CommRing O] {p : ℕ}
  [Fact p.Prime] [Fact ¬ IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

/-!
The bundled perfectoid input keeps the untilt and Fontaine theta maps together.
Their compatibility remains a separate proposition so consumers can choose
which laws to require at a boundary.
-/

structure PerfectoidData where
  untilt : PreTilt O p → O
  theta : WittVector p (PreTilt O p) → O

structure PerfectoidLaws (D : PerfectoidData (O := O) (p := p)) : Prop where
  untilting : UntiltingLaws D.untilt
  theta_compatibility : FontaineThetaLaws D.untilt D.theta

noncomputable def canonicalPerfectoidData : PerfectoidData (O := O) (p := p) where
  untilt := untiltMap (O := O) (p := p)
  theta := thetaMap (O := O) (p := p)

theorem canonicalPerfectoidData_laws :
    PerfectoidLaws (canonicalPerfectoidData (O := O) (p := p)) := by
  exact ⟨canonicalUntiltingLaws, canonicalFontaineThetaLaws⟩

end JoshiTeich.Prologue.Perfectoid
