# 有限高度求和的来源与验收

对于给定的曲线供应数据 \(P\) 和三足点 \(x\)，令 \(F\) 和 \(E/F\) 由 \(P.\mathrm{curve}(x)\) 给出。目标定理断言 \([F:\mathbb Q]\,P.h(x)=h_{\mathrm{fin}}^F(j(E))\)。左端的高度由实际局部高度记录给出。右端在同一个 \(F\) 上以有限处绝对值的正部对数求和。后续高度归一化证明使用此等式，再沿有限扩张和数域同构搬运，才得到三足点域上的公式。 [目标声明](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FiniteHeightSum.lean:31) · [下游消费者](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_HeightNormalization.lean:23)

| 参考工程 | 目标中的对应 |
| --- | --- |
| 曲线域上有限高度求和 | `finrank_mul_h_eq_finHeight` 的完整命令在固定来源、源端重放及目标中逐字一致。 [来源](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Height.lean:582) · [源端重放](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-source-replay-v104-20261117/source-project/B1SourceReplay.lean:1673) |
| 局部高度乘以正的域次数 | `LocalHeightData.deg_mul_height` 的命令逐字移植。 [来源](/home/admin-wsl/Coq/abc/refer/iut/Iut/Implication/PrimeSelection.lean:187) · [目标](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FiniteHeightSum.lean:14) |
| 在覆盖支集的有限集上计算有限高度 | `finHeight_eq_sum` 的支集包含条件由良好约化处贡献为零验证。 [来源](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Height.lean:104) · [目标](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodFiniteHeightSupport.lean:41) |
| 乘法约化处及其补集上的局部公式 | 两式通过跨版本完整类型和证明核对。 [来源](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Height.lean:558) · [跨版本回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-local-height-correspondence-20261119/round-ci-023091-faa7fb06-result.json) |

## 已有验收

- 目标叶检查 `ci-019565-ab7fd8e4` 和 `.olean` 产物 `ci-019567-3b9e0ec7` 均成功。 [叶检查回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-finite-height-sum-leaf-v252-result.json) · [产物回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-finite-height-sum-artifact-v252-result.json)
- `ci-019571-421f1ca2` 通过 Checks、ImportAudit、Act1Scene1、AxiomAudit 与目标模块全部十项声明的公理检查。主定理只依赖 `propext`、`Classical.choice` 和 `Quot.sound`。现有 41 个目标及依赖 `.olean` 与一份目标源码匹配该回执。 [目标聚合和公理回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-finite-height-sum-review-v252-result.json)
- `ci-018560-1db29f6e` 提供完整源端类型和证明。原参考提交为 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，原工具链为 Lean 4.32.0。源端表达式来自 Lean 4.35.0-rc3 下的重放。目标工具链为 Lean 4.33.1。各任务的输入版本、退出码、诊断、时间与内存见绑定记录。 [源端表达式回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-source-actual-closure-v112-result.json) · [输入与回执](input-bindings.json)

## 跨版本审查

用 `review/file` 提交 `AuditFiniteHeightSumCorrespondence.lean`。`B1_FINITE_HEIGHT_SUM_REVIEW_CONFIG` 指向 `review-config.json` 的绝对路径。配置中的来源输入和两个审查输出均使用绝对路径。若移动草稿，更新这三个路径。主定理的完整来源类型和证明均从 `source-facts.jsonl` 读取。 [Lean 审查草稿](AuditFiniteHeightSumCorrespondence.lean) · [审查配置](review-config.json)

审查要求完整类型与绑定位置相同。审查分别核对两份证明项在目标内核中具有完整目标类型，收集它们的公理和直接引用差异。证明项的定义等价使用 Lean 的证明无关性。审查将直接依赖解析为目标环境中的声明。源端的 `LocalHeightData.deg_mul_height` 是归档导出边界，现有审查草稿保留这项直接依赖。 [依赖映射](review-config.json)

独占审查 `ci-023485-b07b9069` 通过，退出码为 0。在目标 Lean 4.33.1 中，`finrank_mul_h_eq_finHeight` 的完整类型匹配，两份证明项均具有完整目标类型且内核判定定义等价。源端和目标端均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。墙钟 65.01 秒，CPU 63.80 秒（用户态 4.93 秒，系统态 58.87 秒），进程树峰值 RSS 4.72 GiB。输入版本和摘要见回执。私有平台验收仍待取得。 [审查回执](round-ci-023485-b07b9069-result.json) · [完整表达式证据](cross-version-expressions.jsonl) · [审查结果](cross-version-result.json) · [独立三语读回](independent-readback/README.md)
