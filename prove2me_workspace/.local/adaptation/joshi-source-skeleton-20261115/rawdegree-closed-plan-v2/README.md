这是 raw-degree 单元的实际合并计划，输入为 `ci-015177-d5a5d8e7` 的 355-name 子图和 `ci-015284-7aab879b` 的递归 frontier 图。所有输入文件及来源源码均记录 SHA256、job 和可用 schema。此轮没有执行编译、CI、API、平台上传或主区修改。

355 与 462 的交集为 345，合并为 **472 条声明、28 模块**。重叠声明的 kind/module/typeDeps/definitionValueDeps/theoremProofDeps/apiDeps 逐字段相同。原来的 14 个 local frontier 已全部解析，增量图递归遍历的本地 type/value/API/实例及 theorem-proof 边在合并图中没有遗漏的本地常量。`resolved-frontiers-and-remaining-work.json` 已移除旧的 14-name 待办，保留其真实 kind/module/axioms。

这里“本地常量闭包完整”只指 actual built declarations 的图闭包；还没有生成或验收平台 Definitions、迁移后的类型身份、完整源码 parser 范围或闭合证明移植。没有把 472 条都变为 theorem。互斥分类为 91 definitions、191 structure API、108 generated companions、14 具源码实例、67 既有闭合 proof helpers 和 1 条 raw-degree 根定理。

`merged-declarations-and-consumers.json` 包含每个声明的 actual job、source path/hash/whole-declaration range、owner、direct consumers、完整 actual type/value/API/proof dependency names。baseline 根的原完整 type 仍由 accepted v3 类型工件保存；其他 exact type/Expr/body 没有猜造，仍待 selected exporter。`updated-module-bundle-dag.json` 为合并后的 28 模块选择性 bundle 图，已检查无环。它包括实际 source theorem proof dependencies，不是整文件移植表。

增量的 462 行均有真实 `collectAxioms`，全部仅含 `propext`、`Classical.choice`、`Quot.sound` 的子集；没有 `sorryAx` 或其他异常公理。尚有 10 条 baseline-only 声明未逐条输出 actual axioms，其中包括 raw-degree 根、`logSum`、`iutInitialThetaQPilotData` 和 `QPilotData.absLogQ/logQ` 等。它们在 `pendingActualAxioms` 中准确列名，缺失不记为零，也不以 helpers 的公理结果代替根公理审查。

原要求的 442 external owners 已全部实际解析。合并后 theorem proof 带来 1085 个不同外部名字，其中 1040 已有 Env 模块归属：867 来自 Mathlib owner 模块，173 来自 Init owner 模块，合计 252 个实际 owner 模块。另有 **45 个名称**来自旧根证明及 baseline-only 定义，目前没有模块归属回执；它们逐名留在 `precise-external-import-map.json`，不按名字猜 Mathlib。这 45 个是外部 owner 查询尾项，不是新的 local proof debt。图中没有未解析的本地常量。

可复用载体候选共 264 个名字，见 `existing-platform-reuse-candidates.json`。其中 131 个有当前 compiled target batch 的真实名字，133 个来自 accepted prior identity map。例子：

| actual Joshi source | 既有 target 名候选 | 当前 Definitions import 候选 |
| --- | --- | --- |
| `JoshiTeich.ReferenceIut.InitialThetaData` | `AbcAdaptation.Reference.Iut.InitialThetaData` | `Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Basic` |
| `JoshiTeich.ReferenceIut.AnabelianGeometry` | `AbcAdaptation.Reference.Iut.AnabelianGeometry` | `Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Orbicurve` |
| `JoshiTeich.ReferenceIut.TateStructure` | `AbcAdaptation.Reference.Iut.TateStructure` | `Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateStructure` |
| `TateCurvesTheta.TateParameter` | `AbcAdaptation.Reference.TateCurvesTheta.TateParameter` | `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_QParameter_Basic` |

这些只是具有实际名称与来源证据的复用候选。既有 Iut→平台身份不自动证明 JoshiTeich.ReferenceIut→平台身份；必须核对实际 encoded names、全部字段、universe/instances、定义体和完整类型。尤其保留现有 `algebraModK/towerModK`、处限制和坏处条件的一致性债务。没有从 local Definitions 文件存在推断平台发布状态，没有按同名等同两个数学 carrier。

需要导出的项目特有材料为 165 行，分布于 9 个实际模块，见 `new-project-export-list.json`：`Prologue.Arithmetic.Basic`、`Prologue.Theta.Tate`；`IutQSourceContract`、`IutTateValuation`、`IutInitialThetaBadPlaceFiniteness`、`IutInitialThetaBaseQPilotSource`、`IutInitialThetaLinkSource`、`IutInitialThetaQRootAccounting` 和 raw-volume 文件中选定 raw q 定义及根定理。165 内含 45 generated companions、58 API，实际应随原结构/定义再生，不能按行数创建 Definitions。项目特有不表示每一行都为原创作者代码；逐模块 source headers 与现有 port 通知必须保留。

另有 43 行参考材料尚无已核对复用目标，仍应导出或解析精确复用项。显著者是 `ReferenceIut.QPilotData`、`absLogQ`、`logQ`、reduction/valuation helper 链，以及 Tate `norm_q_eq_pow_orderNat/toOrdered_orderNat` 等现成证明。它们不是新数学证明义务，也不能为了省略依赖而改成自由实数或公理。

后续工作严格限于：补 45 个外部 owner 与 10 个 actual axiom 输出；对实际 472 名中需要的 original source commands 做 exact type/definition/proof/body 与 Stage2 parser/ref 导出；验证 264 个候选重用项的 source/target typeidentity；据此选择性生成 Definitions 和 raw-degree 的已有 proof。当前交付到此结束，不继续研究数学证明。论文 theta locus/BK/measure/normalization、字面 cor312 和 G1–G4 的状态不受此图闭包改变。
