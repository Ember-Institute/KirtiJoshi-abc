七条纯数值命令草稿，状态为 `source-bound-static-drafts-CI-pending`。未编译、未调用 MCP-CI/API/Git，主工作区只读。未包含已交付的 `assembly`、`c2_final`。没有独立 readback 或验收声明。

| 原命令 `Iut.` 后缀 | 原模块后缀 | 完整 AST command index | 真实原 consumer `Iut.` 后缀 |
|---|---|---:|---|
| `log_bound_ell` | `Corollary22` | 10 | `Corollary22Inputs.c2` |
| `log_le_four_mul_sqrt_sqrt` | `Corollary22` | 7 | `epsilonE_le`, `Corollary22Inputs.c2` |
| `log_le_half_of_pos` | `Corollary22` | 9 | `Corollary22Inputs.c2` |
| `log_le_self_of_pos` | `Corollary22` | 8 | `epsilonE_le`, `log_ell_bound`, `Corollary22Inputs.c2` |
| `log_pi_le_two` | `Theorem110` | 9 | `Theorem110Invariants.theorem110` |
| `log_pi_nonneg` | `Theorem110` | 10 | `Theorem110Invariants.theorem110` |
| `sum_affine_quadratic` | `Theorem110` | 8 | `Theorem110Invariants.sum_arch`, `Theorem110Invariants.sum_capsuleBound` |

`Drafts/` 有七个 `AbcAdaptation.Reference.Iut.<原短名>` 草稿。`RootOnly/` 有七个保留原 `Iut.<原短名>` 的小输入。每个文件只含一个原声明；声明、docstring、签名和证明体均未编辑。外层添加目标 namespace，并记录 imports/context 缩减通知。原版权头及 Apache LICENSE 保留。

`manifest.json` 记录输入 SHA、每条 whole-AST command、binding/signature/proof 的原坐标与生成坐标、原仓库坐标的配置插入逆映射、逐字 identity SHA、精准 Mathlib imports、原公理与实际 consumer。`OriginalCommands/*.json` 保存该真实命令的完整 AST、上下文 AST 和原编译器图记录；`.command.lean`/`.signature.lean.txt` 保存原命令与显式签名。`SOURCE_LEDGER.json` 记录生产者至实际 consumer，canonical integration 标记 false。

抽取依据是已接受的 parser job `ci-014817-8a1bb50d` 及 source-review，使用原 `main-proof-tree.json` 中的 19 命令集合。生成器仅复用上一批 `generate_numeric.py` 的 byte/range 辅助函数；没有新增 Lean parser/oracle 或正则切分命令。所有七条的项目 `typeDeps`/`valueDeps` 为空；原编译器图无 `sorryAx`，仅含 `propext`、`Classical.choice`、`Quot.sound`。

Corollary22 上下文保留原 option、`namespace Iut`、universe、`open Finset Real`、对应 `end Iut`。Theorem110 保留原 option、namespace、universe、对应 `end Iut`；移除原 `open NumberField` 与 `AG`/`TG` variable 命令。完整原上下文 AST 和移除的两个 command 均在 metadata，语义等同性待 actual Expr 核对。

后续由主智能体统一 MCP-CI：先用现有 `QueryNumericSourceFacts.lean` 与 `PendingCIConfigs/original-source-facts.json` 导出七条 actual original Expr；再用现有 `ExtractSmallNumericOracle.lean` 与七个 `small-source-*.json` 分别核对 RootOnly。配置只准备、未提交，输出目录为本临时目录。搬入实际主工作区后需更新配置路径和 SHA；不要直接以本临时目录冒充主工作区。原/小输入/目标 compiler type identity、精准 import 的编译充分性、目标 exact-text 编译、公理审查、下游 canonical wiring 均 pending。不得把本批静态 identity 当成这些验收。
