# 许可证和版权登记

## 当前状态

`ArithmeticTeichmullerSpaces/Act1Scene1/IutTateTorsionResidue.lean` 和
`IutTorsionCardinality.lean` 移植了 `refer/iut` 中 Tate quotient residue 论证以及
rank-two global torsion 到 local torsion 的基数传递，并保留原始版权头和 Apache-2.0
声明。其他已登记的 IUT 改写保留各自的 source-id、来源路径和改写范围。

本工程的项目许可证尚未在 A0 选择。选择后应在本文件记录许可证名称、版本和适用
范围，并在工程根目录放置完整许可证文本。

IUT 移植使用的 Apache-2.0 正文位于工程根目录 `LICENSE`；该文件登记移植代码的
第三方许可证文本，不决定本工程其余原创文件的项目许可证。

## 参考工程

- 参考路径：`refer/iut`
- 参考提交：`d9465c111ec4073709f67e9fccec7e3eb374a816`
- 许可证文件：`refer/iut/LICENSE`
- 许可证：Apache License 2.0
- 移植文件：`ArithmeticTeichmullerSpaces/Act1Scene1/IutTateTorsionResidue.lean`、
  `ArithmeticTeichmullerSpaces/Act1Scene1/IutTorsionCardinality.lean`
- 来源文件：`refer/iut/Iut/Cor312/ThetaData/TateStructure.lean`、
  `refer/iut/Iut/Anabelian/TateTorsion.lean`、`refer/iut/Iut/Anabelian/Torsion.lean`、
  `refer/iut/Iut/Anabelian/LocalInputs.lean`
- 改写范围：两文件分别移植抽象商群均匀化/residue/root-class 论证和 rank-two global
  torsion 经 injective local map 得到局部基数下界的论证；未移植椭圆曲线坐标 pinning、
  实际 `AdmissiblePrimeData` 构造或 `TateCurvesTheta` 依赖。两个目标文件均保留 iut
  原始版权及许可证头，source-id 分别为 `IUT-COR312-TATE-TORSION-RESIDUE` 和
  `IUT-COR312-TORSION-CARDINALITY-TRANSFER`。

参考工程不是本工程的上游或依赖。只有在逐文件审查后才允许移植代码。移植时必须
同时记录：原文件路径、原提交、原版权声明、Apache-2.0 通知、目标文件、改写范围
和对应的 `source-id`。

## Mathlib4

Mathlib4 通过本地 path 依赖使用，不复制其源文件到本工程。版本固定为 commit
`389347a7c1cfa76f6bd5be2ca35d4cb621610ad3`；其许可证和版权信息由本地 mathlib4
发行目录负责。
