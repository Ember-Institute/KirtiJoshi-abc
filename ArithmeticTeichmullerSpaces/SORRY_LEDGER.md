# Prologue 证明债务登记

每条 `sorry` 都是有来源的命名构造定理。接口文件不调用这些定理；Act2 负责逐项
替换证明并保留来源和陈述忠实度记录。

| source-id | 声明 | 文件 | 来源位置 | fidelity | 依赖 | Act2 归属 | 状态 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `JT-ATS-III-adelic-theta-link` | `build_adelicThetaLink` | `Prologue/Obligations/Constructors.lean` | `refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | conditional interface | `AdelicThetaLinkData` | `Act2.Prologue.AdelicThetaLink` | open |
| `JT-ATS-III-theta-lift-log` | `build_thetaLiftLog` | `Prologue/Obligations/Constructors.lean` | `refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | conditional interface | `AdelicThetaLinkData` | `Act2.Prologue.ThetaLiftLog` | open |
| `JT-ATS-III-packet-collation-hull` | `build_packetCollationHull` | `Prologue/Obligations/Constructors.lean` | `refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | conditional interface | `AdelicThetaLinkData` | `Act2.Prologue.PacketCollationHull` | open |
| `JT-ATS-III-volume-transfer` | `build_volumeTransfer` | `Prologue/Obligations/Constructors.lean` | `refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | conditional interface | `AdelicThetaLinkData`, packet/hull collation | `Act2.Prologue.VolumeTransfer` | open |
