本计划直接消费主智能体已通过的 `ci-015177-d5a5d8e7` 的 `query-v3/declgraph.jsonl`，不是重复旧 96-node 静态清单。此轮仅生成只读分析工件；没有编译、CI、API、上传或主区修改。

三根实际完整 `elaboratedType` 已逐项审读，和原计划吻合：raw-degree 仍量化完整 `AG/TG/D`，结论是实际 raw q-sum 等于全局次数乘 actual reference `absLogQ`；actual-bound 仍使用同一 `D` 构造的 `length/hullVolume/logSum`；条件 Corollary 保留完整 `O/p` 类型类、theta、route、thetaBase、heightData、ramification、`X : AnalyticInput ...`。实际结构 API 有 `AnalyticInput` 的全部七字段及 constructor。字段独立完整类型尚待 selected exporter，不能把源码读回当作已完成迁移后的类型等同性检查。

1073 行的互斥主分类如下；角色旗标可以重叠：

| 主分类 | 行数 | 平台处理 |
| --- | ---: | --- |
| 已选三个 theorem | 3 | 仅这三条是本轮候选平台 theorem nodes |
| definition material | 273 | 必要定义；按声明闭包抽取 |
| structure/inductive API | 349 | 随完整结构/归纳声明生成，不能逐字段机械升成 theorem |
| 无源码跨度的 generated companions | 379 | 先保留依赖，随后随原声明再生；不单独上传 |
| 有源码跨度的 registered instances | 31 | Definitions 中保留；总实例数是 67，其余 36 行归在 generated companions 主类 |
| 有源码跨度的非 API def-embedded theorem | 36 | 必须带既有闭合 proof；另外 3 条同类 theorem 首要角色为 instance，故全部具名非 API direct targets 共 39 |
| 其他 infrastructure theorem type helpers | 2 | private source helpers；精确抽取和闭合证明处理待完成 |

底层 kind 原始统计为 446 def、487 theorem、52 inductive、52 ctor、36 rec。Lean 的 theorem-kind 包括 Prop-valued field accessors、证明 companion 和 theorem-valued instances，487 不等于 487 个新数学节点。

617 条实际 definition-value→theorem 边消费 352 个不同目标：290 个 generated proofs、23 个结构 API、39 个有源码的非 API theorem。逐边 consumer/target、实际模块、owner、源码范围、source-id 均在 `definition-theorem-consumption.json`。62 个非 generated direct targets 的源码整体范围和现成 proof-body 证据在 `named-def-embedded-source-evidence.json`，范围来自编译器；它们不是 parser 的内部 proof cut 位置。每个定义所需 theorem 都应以已有闭合证明随 Definitions 供应，或随原结构/原定义再生；不能换成 Open stub。

下一最小单元建议先做 `JNEXT-RAW-DEGREE`：不补实例时为 268 行，保留 reached-module instance 固定点后为 **355 行、25 模块**；其中 82 行无源码跨度。actual-bound 单根为 812 行/73 模块，完整条件 composer 单根为 1047 行/87 模块。三根并集加实例为 1073 行/89 模块。三根基础 type/def/API 闭包为 935；module-instance 补根多出 138 行，但没有引入新模块。`instance-expansion.json` 对额外声明按实例给出归因（各实例的归因可能重叠）。

`next-minimal-export-unit.json` 已列出 raw-degree 单元的 exact names、25 模块依赖顺序、待导出的 type/definition-body、theorem/projection/regeneration proof 和 parser 文件。该小单元现有 theorem proof 闭包还出现 14 个未导出的 local exact names，包括 `logTerm_eq_order_term`、`base_qOrder_eq_initialTheta_qOrder` 和实际 arithmetic/Tate helpers。这些名字并不都必然是 theorem；当前图只证明它们被 theorem proof 消费。后续 exporter 应由 Env 核对其真实 kind/module/type，并继续递归所需既有 proof/definition 依赖。

候选 Definitions bundle DAG 按实际模块的选择性声明子集形成：89 个候选 bundle、476 条已知跨 bundle 依赖，依赖顺序和逐声明边证据已保存于 `candidate-bundle-dag.json`。检查确认当前图无环，且没有 Definitions 基础材料依赖三个 Open roots。DAG 合并同模块的 structure/constructor/projection 内部循环。它包括当前已知的 signature/definition/API 及基础 theorem proof 边；尚未解析的 proof-frontier 可增加模块与边，因此后续必须重新计算，而非把此候选图当成完成的编译闭包。没有打包 89 个整文件。

三个 theorem 的组合关系保留：

- raw-degree 的既有 proof 仍从实际 norm/order、finite arithmetic-degree accounting 得出；对应 helper proof frontier 尚需按 exact names 补齐。
- actual-bound 的实际 root proof 直接引用 `negAverageAbsLog_actualVolume_ge_neg_logSum`、length/tuple/tuple_liesOver/length_pos。源码 helper 链通过 `reference_le_logSum` 消费 raw-degree；此间接组合边有源码证据，完整 compiled helper export 仍 pending。
- 条件 composer 的实际 root proof 直接引用 actual-bound；完整真实 `AnalyticInput` 类型不变。现有定义可将两种结论读作 definitional equality，但迁移命名空间后的 reduction 仍需正式验证。

外部及 deferred proof frontier 合计 1375 个不同 exact names：139 个 local names 只出现在 deferred theorem-proof 边；其余 1236 为 Core/Mathlib/其他依赖边，58 个显式处于 `Mathlib.*` namespace。所有 incoming edge 及 edge kind 已保存于 `external-and-proof-frontier.json`。没有猜测 `Real`、`Eq` 等普通名字的精确归属模块；后续 Env `getModuleIdxFor?` 应给出 authoritative module。这项模块归属导出不需要打印所有巨大 type/value。`closed-proof-frontier-plan.json` 单列基础材料需要的下一批 local names。

后续依次执行：raw-degree 所选精确 type/definition body + 完整结构字段/实例导出；14-name frontier 的 exact module/kind/type/direct-deps 及必需递归 proof closure；25 模块 Stage2 parser/valStart/ref 事实；依据这些事实选择性抽取并复用现成证明，核对 elaborated types、公理和定义无 sorry。当前 `candidateWholeSourceUnits` 只是编译器 range 分组，不作为源码生成位置 oracle。不得用 regex 拆声明或把生成名当人工 theorem 上传。

每个模块的当前来源文件、hash、owner、source-id、literal provenance/license header 及 SOURCE_LEDGER 命中位于 `module-source-map.json`。原三根为项目原创文件，项目许可证未选择的事实仍保持，不把第三方 Apache 文本扩大到原创文件。Joshi 数学来源仍只取原始 III TeX；paper M/J locus、BK/period、真实跨来源 collation、Γ-weighted measure、normalization 与字面符号适配全部保持 Open。此计划不声称论文 cor312、Form2、G1–G4 或平台 abc 根目标已经证明。
