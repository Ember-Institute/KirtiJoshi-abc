# 许可证和版权登记

## 当前状态

`ArithmeticTeichmullerSpaces/Act1Scene1/IutTateTorsionResidue.lean`、
`IutTorsionCardinality.lean`、`IutWeierstrassLocalization.lean` 和
`IutTorsionRationality.lean` 移植了 `refer/iut`
中的 Tate quotient residue 论证、rank-two global torsion 到 local torsion 的基数传递、
Weierstrass affine-point localization bridge，以及由 Galois 表示条件推出的 torsion
fixed-field rationality，并保留原始版权头和 Apache-2.0 声明。其他已登记的 IUT 改写保留
各自的 source-id、来源路径和改写范围。

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
  `ArithmeticTeichmullerSpaces/Act1Scene1/IutTorsionCardinality.lean`、
  `ArithmeticTeichmullerSpaces/Act1Scene1/IutWeierstrassLocalization.lean`、
  `ArithmeticTeichmullerSpaces/Act1Scene1/IutTorsionRationality.lean`
- 来源文件：`refer/iut/Iut/Cor312/ThetaData/TateStructure.lean`、
  `refer/iut/Iut/Cor312/ThetaData/PointMap.lean`、
  `refer/iut/Iut/Anabelian/TateTorsion.lean`、`refer/iut/Iut/Anabelian/Torsion.lean`、
  `refer/iut/Iut/Anabelian/LocalInputs.lean`、
  `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`、
  `refer/iut/Iut/Cor312/ThetaData/LocalConditions.lean`
- 改写范围：前两文件分别移植抽象商群均匀化/residue/root-class 论证和 rank-two global
  torsion 经 injective local map 得到局部基数下界的论证；第三文件将 `iut` 的点映射
  接口适配为 Mathlib `Affine.Point.map` 上的实际 Weierstrass base-change bridge；第四文件
  移植由 basis-compatible Galois representation 推出 torsion fixed-field rationality 的
  条件证明，以及由显式 kernel-openness 证书推出有限维数域的结论；当前新增的窄来源投影
  只复制 `AdmissiblePrimeData` 中用于 q-root 装配的素数、下界、闭包和 torsion basis 字段，
  不移植完整 `AdmissiblePrimeData` 构造或 `TateCurvesTheta` 依赖。四个目标文件均保留 iut
  原始版权及许可证头，并登记各自的 source-id。

参考工程不是本工程的上游或依赖。只有在逐文件审查后才允许移植代码。移植时必须
同时记录：原文件路径、原提交、原版权声明、Apache-2.0 通知、目标文件、改写范围
和对应的 `source-id`。

## Mathlib4

Mathlib4 通过本地 path 依赖使用，不复制其源文件到本工程。版本固定为 commit
`389347a7c1cfa76f6bd5be2ca35d4cb621610ad3`；其许可证和版权信息由本地 mathlib4
发行目录负责。

## S1.307：actual tensor order 与 residue decomposition

- 参考快照：`07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。
- 来源文件：`refer/iut/Iut/Concrete/LocalConstruct/Integral.lean`、
  `refer/iut/Iut/Concrete/LocalConstruct/MaximalOrder.lean`。
- 两来源文件最后提交：`b76207ab8955e68a7408d5d2a770b75a30c3bebf`；Git 作者
  Christian Merten；文件版权和作者为 The iut contributors（2026）。
- 逐文件审查：文件头均为 Apache-2.0，参考 `LICENSE` 与本工程用于第三方移植的
  `LICENSE` 正文一致；保留原通知，不据此选择原创工程其余文件的许可证。
- 目标：`Act1Scene1/LocalCompletionTensorOrder.lean`、
  `Act1Scene1/LocalCompletionTensorResidueDecomposition.lean`。
- source-id：`JT-SCENE1-LOCAL-TENSOR-ORDER-NORMALIZATION`、
  `JT-SCENE1-LOCAL-TENSOR-RESIDUE-DECOMPOSITION`。
- 改写范围：tensor 的 ℤ_p algebra、unit order 乘法封闭性、finite order 元素的
  integrality、integral closure 包含，以及 formally unramified tensor 证明。
  使用本工程实际 completion factors、既有有限 unit lattice 和 Mathlib 的
  reduced Artinian 分解；未复制 junk quotient、参考 hull 或自由 volume laws。
- 目标文件均保留原路径、原提交、作者、版权及 Apache-2.0 通知；无 `Iut` import，
  无参考工程依赖。构建和公理验证记录于 log4 的 S1-BND-307。

## S1.308：normalization finite/compact

- 来源：`refer/iut/Iut/Concrete/LocalConstruct/MaximalOrder.lean`，快照
  `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，原提交
  `b76207ab8955e68a7408d5d2a770b75a30c3bebf`。
- Git 作者 Christian Merten；原文件作者和版权 The iut contributors（2026）；
  文件头声明 Apache-2.0，参考 `LICENSE` 已复核。
- 目标：`Act1Scene1/LocalCompletionTensorNormalizationCompact.lean`，
  source-id `JT-SCENE1-LOCAL-TENSOR-NORMALIZATION-COMPACT`。
- 改写：residue-field integral closure 有限性、injective normalization map、
  有限 integral span 有界与 normalization 紧致性，全部使用 actual Packet、
  S1.307 的 integral closure 和 residue decomposition。
- 保留原路径、提交、作者、版权和 Apache-2.0 通知，无 Iut 导入或参考依赖。
  同单元的 `LocalCompletionTensorNormalizationHaar.lean` 为原创 Haar 构造和比较，
  未复制参考代码。验证见 log4 S1-BND-308；第三方许可证不决定原创文件许可证。

## S1.311：residue spectral norm 与 unit-ball criterion

- 来源：`refer/iut/Iut/Concrete/LocalConstruct/ResidueField.lean`，快照
  `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，原提交
  `fe96f99cae5c6d48d25113163f1b9b388fc35814`。
- Git 作者 Christian Merten；文件作者、版权 The iut contributors（2026）；
  原文件头和 LICENSE 的 Apache-2.0 已在复制前审查。
- 目标：`Act1Scene1/LocalCompletionTensorResidueNorm.lean`，source-id
  `JT-SCENE1-LOCAL-TENSOR-RESIDUE-SPECTRAL-NORM`。
- 改写范围：spectral norm laws 和 minpoly/lifts 积分性单位球判据，改为实际
  tensor residue fields；显式提供 NormedField，不预置 topology/paper norm 身份。
  不复制参考 least hull、free volume 或 junk quotient。
- 保留原路径、作者、提交、版权及许可证头，无 Iut 导入或参考工程依赖。
  同单元 `LocalCompletionTensorResidueBallRegions.lean` 消费本工程实际 region
  decomposition；验证见 log4 S1-BND-311。

## S1.312：discrete spectral radii 与 principal regions

- 来源：`refer/iut/Iut/Concrete/LocalConstruct/ResidueField.lean`，原提交
  `fe96f99cae5c6d48d25113163f1b9b388fc35814`，快照
  `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`；Git 作者 Christian Merten，
  文件版权和作者 The iut contributors（2026），Apache-2.0 已在移植前复核。
- 目标：`Act1Scene1/LocalCompletionTensorResidueNormDiscrete.lean`、
  `Act1Scene1/LocalCompletionTensorPrincipalRegions.lean`。
- source-id：`JT-SCENE1-LOCAL-TENSOR-RESIDUE-DISCRETE-RADII`、
  `JT-SCENE1-LOCAL-TENSOR-PRINCIPAL-RADIUS-MINIMUM`。
- 移植范围：原文件 240–313 的离散值与 least radius 论证，202–235 的单位和
  principal-region norm 判据，适配实际 Packet。两目标保留原路径、提交、作者、
  版权和许可证通知。积分区域 U 的 coordinate-sup least-hull 消费者为本地构造。
- 无 Iut 导入、参考依赖、junk quotient 或自由体积合同；构建及审计见 log4 S1-BND-312。
