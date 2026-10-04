import ArithmeticTeichmullerSpaces.Prologue.Interfaces

namespace JoshiTeich.Prologue.Obligations

variable {K : Type*} [Field K] [NumberField K]

-- source-id: JT-ATS-III-adelic-theta-link
-- source: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md
-- fidelity: conditional interface; construction remains an Act2 obligation
-- owner: Act2.Prologue.AdelicThetaLink
theorem build_adelicThetaLink (D : AdelicThetaLinkData K) : AdelicThetaLink D := by
  sorry

-- source-id: JT-ATS-III-theta-lift-log
-- source: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md
-- fidelity: conditional interface; construction remains an Act2 obligation
-- owner: Act2.Prologue.ThetaLiftLog
theorem build_thetaLiftLog (D : AdelicThetaLinkData K) : ThetaLiftLog D := by
  sorry

-- source-id: JT-ATS-III-packet-collation-hull
-- source: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md
-- fidelity: conditional interface; construction remains an Act2 obligation
-- owner: Act2.Prologue.PacketCollationHull
theorem build_packetCollationHull (D : AdelicThetaLinkData K) :
    PacketCollationHull D := by
  sorry

-- source-id: JT-ATS-III-volume-transfer
-- source: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md
-- fidelity: conditional interface; construction remains an Act2 obligation
-- owner: Act2.Prologue.VolumeTransfer
theorem build_volumeTransfer (D : AdelicThetaLinkData K) : VolumeTransfer D := by
  sorry

end JoshiTeich.Prologue.Obligations
