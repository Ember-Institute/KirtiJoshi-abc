import ArithmeticTeichmullerSpaces.Prologue.Obligations.Constructors

namespace JoshiTeich.Prologue.Obligations.Audit

/-!
This is the debt-side audit for the four named Prologue constructors.  It is
kept outside the public Prologue and Scene import graph so that the debt is
visible without becoming an input to any proof layer.
-/

open JoshiTeich.Prologue

variable {K : Type*} [Field K] [NumberField K]

def registeredSourceIds : List String :=
  [ "JT-ATS-III-adelic-theta-link"
  , "JT-ATS-III-theta-lift-log"
  , "JT-ATS-III-packet-collation-hull"
  , "JT-ATS-III-volume-transfer" ]

theorem registeredSourceIds_count : registeredSourceIds.length = 4 := by
  rfl

-- The declaration checks keep the ledger names synchronized with Lean.
#check build_adelicThetaLink
#check build_thetaLiftLog
#check build_packetCollationHull
#check build_volumeTransfer

-- These outputs are expected to contain `sorryAx` until Act2 closes each debt.
#print axioms build_adelicThetaLink
#print axioms build_thetaLiftLog
#print axioms build_packetCollationHull
#print axioms build_volumeTransfer

end JoshiTeich.Prologue.Obligations.Audit
