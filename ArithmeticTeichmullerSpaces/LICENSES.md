# 许可证和版权登记

## 当前状态

截至 A1.1，`ArithmeticTeichmullerSpaces/` 已搬运三份纯 mathlib 文件：有限平均、
加权平均和非阿基米德对数误差。它们保留原版权声明和 Apache-2.0 许可证通知，并
在本工程中改用 `JoshiTeich.A1` 命名空间。其余工程文件不是这些文件的衍生复制品。

本工程的项目许可证尚未在 A0 选择。选择后应在本文件记录许可证名称、版本和适用
范围，并在工程根目录放置完整许可证文本。

复制文件使用的 Apache-2.0 正文位于工程根目录 `LICENSE`；该文件只作为复制文件的
第三方许可证文本登记，不决定本工程其余原创文件的项目许可证。

## 参考工程

- 参考路径：`refer/iut`
- 参考提交：`d9465c111ec4073709f67e9fccec7e3eb374a816`
- 许可证文件：`refer/iut/LICENSE`
- 许可证：Apache License 2.0
- 已复制文件：`Iut4Sec1/Combinatorics/RangeAverages.lean`、
  `Iut4Sec1/Combinatorics/WeightedAverage.lean`、`Iut4Sec1/Real/LogError.lean`

参考工程不是本工程的上游或依赖。只有在逐文件审查后才允许复制代码。复制时必须
同时记录：原文件路径、原提交、原版权声明、Apache-2.0 通知、目标文件、改写范围
和对应的 `source-id`。

## Mathlib4

Mathlib4 通过本地 path 依赖使用，不复制其源文件到本工程。版本固定为 commit
`389347a7c1cfa76f6bd5be2ca35d4cb621610ad3`；其许可证和版权信息由本地 mathlib4
发行目录负责。
