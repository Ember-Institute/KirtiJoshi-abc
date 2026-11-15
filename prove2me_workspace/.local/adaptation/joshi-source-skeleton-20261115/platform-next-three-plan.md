本轮的下一个可审查单元是三个已有 theorem 的声明与条件组合图；不填 Act2 缺证，不把工程 `Corollary312` 当作 Joshi 原文字面 cor312。

| 顺序 | 原始 exact name | 平台角色 | 必须保留的数学输入 |
| --- | --- | --- | --- |
| 1 | `JoshiTeich.Act1Scene1.InitialThetaRawQ.logSum_eq_degree_mul_reference` | 精确 Open theorem，随后移植既有 proof；raw/degree normalization 的可复用中间节点 | `AG : AnabelianGeometry.{u}`、`TG : TemperedGeometry AG`、`D : InitialThetaData AG TG`；`D` 的所有实例和字段，不改成只供应实数 `R` 的替身 |
| 2 | `JoshiTeich.Act1Scene1.CanonicalActualHull.raw_volume_bound` | 精确 Open theorem；可由现成辅助定理及节点1形成 reduction | 同一 `D`；`length`、selected constant tuple、actual collation/hull volume 的定义体 |
| 3 | `JoshiTeich.Act1Scene1.CanonicalActualHull.corollary312` | 精确条件 composer；由节点2直接归约 | 全部 `O/p` 实例、`D`、theta、route、thetaBase、heightData、ramification、`X : AnalyticInput ...` |

名称先保留原始 exact name 作为本地身份。最终平台名可统一包在现有适配命名空间内；必须由现成 Stage 2 的 reference ranges 机械变换，记录 exact-name map，并做 elaborated type 一致性检查。现在不预设会导致冲突的上传名称，也不从源字符串猜作用域或 binder。

静态源码已经确认的组合边（实际 Env 查询后再确认全部 exact names）：

```
logTerm_eq_order_term + actual local norm/order + finite degree accounting
    → JNEXT-RAW-DEGREE
    → reference_le_logSum
VBadThetaLogCollation.negAverageAbsLog_volume_eq_referenceLhs
    + reference_le_logSum
    → negAverageAbsLog_actualVolume_ge_neg_logSum
    → JNEXT-RAW-BOUND
    → JNEXT-COR-COMPOSER
```

节点2的既有 proof 是用 `negAverageAbsLog_actualVolume_ge_neg_logSum` 特化 `length D`、`tuple D`、`tuple_liesOver D` 和 `length_pos D`。该 helper 的既有 proof 改写 actual Haar log identity，再用 `reference_le_logSum D`；后者改写节点1，使用 `[D.F : ℚ] ≥ 1` 和实际 `absLogQ > 0`。这些已有证明可作 inline helpers，不要求为一行包装器再发布 theorem。

节点3的既有 proof body 是 `raw_volume_bound D`。导入节点2后可以形成同类型的 top-level `theorem solution`，其余 type/definition 由 Definitions 提供。不能为了缩短类型删 `AnalyticInput`，不能把 `cost D = ∑ period` 改成 `Corollary312 ...` 的别名字段。节点3现有 statement 的 conclusion 按定义展开等于节点2，真实源代码已使用该 definitional equality；平台重命名后仍必须由编译器检查。

Definitions 的准备分三层，层内和跨层顺序以 compiled graph 为准：

1. 复用已经迁移的实际参考 carriers：`AnabelianGeometry`、`TemperedGeometry`、`InitialThetaData`、Tate data、finite places、q-pilot source 与 arithmetic weight。逐项比较实际 elaborated type，不能只凭同名或迁移文件存在认定两种 scalar tower/处集限制一致。
2. 最小 actual q/hull carrier：`InitialThetaRawQ.Index/factor/logTerm/logSum`、canonical `length/tuple/tuple_liesOver`、实际 log-image collation、tensor packet、normalization hull、Haar volume、`hullVolume`。它们采用真实完成域和根，不能降成自由 `ℝ` 参数；被定义体引用的 theorem 必须内含已闭合证明。
3. 条件 composer carrier：`ThetaPilotData`、cost packet/link、`PerfectoidPlaceData`、bridge 与法律、`AnalyticInput` 全字段、`toCanonicalInput`、`Scene1Input` 和四项 producer、`Corollary312Data`、canonical `data`、`Corollary312`。这层仅为节点3陈述所需，不把未定义的 paper loci 混入基础定义。

当前 query 的 signature stage 不递归 theorem proof，但输出完整 `theoremProofDeps` frontier。后处理须先把 frontier 分为：

- 被 definition body、instance body 或 definition所需证明直接消费的 theorem：其闭合 proof 和递归 proof dependencies 属于 Def-embedded theorem 闭包，不能引用 Open theorem stub。
- 被节点的 theorem proof 消费的 theorem：按数学复用价值决定 theorem node 或 inline helper。选中的三根保持可见，其余一行投影/包装不机械提升。

结构的 constructor 和全部 field projection API、包括 Prop-valued fields 的 theorem-kind accessor，继续随结构整体供应，不能误作独立节点。spanless compiler auxiliaries 要先遍历其依赖，再作为 parent regeneration 处理。实例按已经可达的 participating modules 补根并取不动点；不把整文件的全部 unrelated theorem proof 自动带入。

平台编排顺序是最小 Definitions → 三条 Open theorem 的精确声明 → 节点1既有 proof移植 → 节点2 reduction/既有proof → 节点3 reduction。Open stub 与 Definitions 的信任边界严格分开。每次正式声明生成必须取 Stage 2 `decl/valStart/ref` 位置，不用手工切 proof 或字符串替名；读回检查 source 与迁移 types，之后才准备中英日 metadata。全流程在用户既有授权范围内继续推进；本文件本身不触发发布。

保留的显式开放父债务是：共同真实 seed/geometry/holomorphoid、H¹ₑ/crystalline/BK/Fréchet period、真正跨来源 collation、paper M/J loci、Γ-weighted measure/archimedean normalization、selected/omitted mass 和字面符号适配。这里三条 theorem 的上传/归约不使这些父债务改变状态，也不为 `abc.goal.lt_constant_mul_fix` 提供一个新的无条件证明路径。
