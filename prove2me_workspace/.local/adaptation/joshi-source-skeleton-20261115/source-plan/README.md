建议下一单元只登记三条已有真实声明：

| ID | 现有声明 | 精确输入 | 消费者／用途 |
| --- | --- | --- | --- |
| JNEXT-RAW-DEGREE | `InitialThetaRawQ.logSum_eq_degree_mul_reference` | 任意既有 `InitialThetaData AG TG`，保留其全部类型及实例 | `reference_le_logSum`、canonical q-sum accounting；揭示 raw sum 的全局次数因子 |
| JNEXT-RAW-BOUND | `CanonicalActualHull.raw_volume_bound` | 同一 `D`；实际 completion norm、selected tuple、ordinary-log hull/Haar volume 均由定义固定 | 下行一条；不是自由实数 volume 下界 |
| JNEXT-COR-COMPOSER | `CanonicalActualHull.corollary312` | 同一 `D`、`O/p` 完备性实例、theta、route、thetaBase、height、ramification、完整 `AnalyticInput` | Fontaine consumer 与 Summary consumer；proof body 正是 `raw_volume_bound D` |

这些源码都有既存 proof body；可先登记为 Open 精确陈述，再复用已闭合源码 proof。这里没有新增 Act2 证明。没有重复提升 `corollary312_of_transferLogBound`，因为它和第三条同型，只是较长的另一条证明路径。

精确源码类型和全部 section context 位于 `next-unit.json`。`readback-input.lean` 以新名称保留同一参数和类型，供后续中英日读回；它未编译，也不是可直接上传的 Definitions payload。原始源码片段、哈希和 Joshi 原文位于 `source-evidence.json`。三条源文件哈希与既有 96 节点审查记录一致。

最关键的数值区别是：设 `d = [D.F : ℚ]`，`R = ReferenceIut.QPilotData.absLogQ (...)`，`n = length D`，则现有源码给出 `rawLogSum = d * R`、`-log(hullVolume) = n * R`。第二条因此给出 `-R ≥ -d*R`，保留一般数域次数。它不是把所选根集直接当论文完整处集，也不是证明任一论文 theta locus 的体积。

第三条必须保留 `AnalyticInput` 的七项：`placeData`、`bridge`、`thetaScaling`、`periodMap : ∀ i, theta.period i = theta.liftedLog i`、`normalization : cost D = ∑ i, theta.period i`、`perfectoidBridge`、`theta_log_shell : ∀ i, theta.liftedLog i = Real.log (theta.norm i)`。不能把这些条件删掉后发布无条件结论，也不把这些法律本身称为共同来源存在性。

四个 Scene1 producer 的实际路径是 `AnalyticInput` → `toCanonicalInput` → `CanonicalInitialThetaScene1Input.toScene1Input` → `Scene1ProducerLaws`：

- `AdelicThetaLink` 的 valuation scaling 来自 canonical Tate；theta scaling、period map 和 cost normalization 仍消费上述显式条件。
- `ThetaLiftLog` 消费 `theta_log_shell` 及 theta scaling 的非零性。
- `PacketCollationHull` 由 actual cost packet support/nonzero 构造；源代码的 Empty 额外 hull charge 不表示丢弃实际 hull，因为每个 packetWeight 已是实际 collated hull cost。
- `VolumeTransfer` 由 actual local Haar costs 的有限和构造。它提供工程 cost accounting；paper measure 身份仍开放。

Prologue R5 继续只供载体、局部 Tate、FirstAxiom、PerfectoidBridge 法律。四个全局来源法律的 owner 为 Scene1。`ProducerContracts.lean` 里的 `xxxLaw : Prop` 只选择命题，不供应具体论文法律及其证明，因此本单元不使用它们替代下列开放节点。

Joshi 原文对应只引用 `refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex`：`th:moccor-Mochizuki-form2`（3617–3632）同时声称 M、J 两个 locus 的体积下界；`cor:cor312`（3647–3650）字面右端为 `-∑ log |q^(1/(2ell))|`。在实际 contracting roots 下其为正，而左端非正。现有第三条的 qLogTerm 是 `-log factor`，最终右端为 `∑ log factor`，即 volume-derived 临时读法。原文字面陈述、此临时读法和二者适配义务须分别登记。原文 label 中的作者名不是本单元引用 Mochizuki 文献作 Joshi 来源。

保留以下显式 Open 定义／身份债务；目前没有实际完整 Lean carrier，故不能把它们伪装为已有精确 theorem type：

| Open ID | 必须固定的数学对象与精确缺口 | 父义务 |
| --- | --- | --- |
| JPAPER-LOCUS-MJ | 从同一算术 seed/holomorphoid、H¹ₑ/crystalline/BK class、log-shell、完整 theta index 和真正 multilinear tensor map 定义 `Theta_M`、`Theta_J`；actual Unit-indexed ordinary-log collation 不是它们的定义 | O06–O09、O13 |
| JPAPER-MEASURE | 在上述实际 tensor receiving spaces 定义论文 Γ-weighted Haar/hull volume，Γ 为逆相对完成次数；保留可测、有限支撑、无穷处和 procession normalization | O10–O12、O14 |
| JPAPER-IDENTITY | 在已固定载体之间给出实际 theta-class image、hull containment/identity 和测度传递；不能输入一个与 Form2 同结论的 renamed field；不得设任意 `thetaVolume : ℝ` 代替该构造 | O13、O14 |
| JPAPER-SIGN-Q | 字面／volume-derived 符号适配；raw、degree-normalized、residue/paper-normalized、`2ell`、`p*`、selected/omitted mass 在同一来源上的身份 | O15、G1/G3 |

这些是明确的 Open definition debts，而不是本单元 composer 的隐藏数学假设。Form2 的两条下界、字面 cor312、G1–G4、平台根 `abc.goal.lt_constant_mul_fix` 继续 Open。

根查询位于 `QueryJoshiNextRoots.lean`，配置见 `query-config.json`。它沿 actual compiled Env 的三条 root 类型、定义体、现成 theorem proof 和 structure constructor/field API 遍历；分别输出 `typeDeps`、`definitionValueDeps`、`theoremProofDeps`。后处理必须区分：theorem proof 侧依赖可作 theorem/inline helper；被定义体使用的 theorem 必须以已闭合 proof 随 Definitions 供应，不能导入 sorry-stub。spanless auxiliaries 在 reachability 后才丢弃。实例以已可达模块为范围补根并取不动点。脚本仅是待主智能体 MCP-CI 验证的草稿，本子智能体没有编译。

`static-import-closure.json` 的 232 local / 113 external 只是整文件导入的保守旁证，**不是最小适配闭包或待移植文件清单**；没有打包任何 232 文件。未触及 untracked scratch、Act2、Scene2 或 Prologue/Obligations。必要最小闭包必须以 compiled query 的实际声明结果确定。现有适配 Definitions 未提供 InitialThetaRawQ/CanonicalActualHull/Scene1Input/AnalyticInput，因此先做该最小闭包提取；现有已移植 Reference carrier 的重用也需要显式 namespace map 和 elaborated type 一致性检查。

后续三语读回待定术语：`uniformizer`、`collation`、`hull`、`log-shell`、`period`、`marking`、`holomorphoid`、`arithmeticoid`、`degree-normalized`／`paper-normalized`。读回应明确 ordinary log 与 normalized BK log 的区别，不把 raw hull volume 翻译成论文 theta volume。
