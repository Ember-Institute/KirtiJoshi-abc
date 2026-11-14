# 有限分歧来源审计补充与纠正

结论：`finiteCoordinateRamification` 已由当前既有 `noncriticalRamificationFinite` 完整供应。本 child 不存在尚未移植的来源 proof，也无需新增 Act2 数学。先前“导数只有 Basic 层、Local/Order 尚缺”的判断遗漏了现有 Theorems 层，本补充明确取代该判断。

最小集成只需导入 `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalRamificationFinite`，然后使用：

```lean
noncriticalRamificationFinite M hDVR M.u M.transcendental_u
```

这与草稿 child 的结论定义相同，不改变 `M.K`、`Place M.K`、`ramIdx` 或 `ord`。child 的 `hRF` 可按原接口保留，既有一般定理本身不需要它。既有 tmp Lean 设计保持原样，本次仅补来源审计；草稿中的 `sorry` 不再代表真实数学债务，主智能体可按上式复用既有证明关闭，且不 Deprecated 该节点。

最小证明依赖是：

1. `noncriticalRamificationFinite` 把分歧处放入“实际 ψ 的极点 ∪ 实际导数不保持 O_P 的处”。
2. `noncriticalDerivativeBadPlacesFinite` 由实际 `chartRing ψ` 对 `ℚ[ψ]` 的有限模生成元、各导数的有限极点、实际局部化表示推出后一集合有限。所需 helper 已在 `Def_FermatCurveDerivationLocalization`。
3. `noncriticalRegularRamifiedDerivNotMem` 用实际 uniformizer、剩余 minpoly、链式法则和 `derivAlong_eq_unit_mul_pow_of_aeval` 证明正则分歧处属于后一集合。
4. 所需 `CurveDeriv` Local/Order 链的九个公开 theorem 已全部在当前 Theorems 文件中有完整 proof body：`exists_irreducible_valuation_lt_one`、`valuation_aeval_derivative_eq_one`、`exists_pow_succ_mul_derivAlong_not_mem`、`exists_eq_div`、`exists_pow_mul_derivAlong_mem_integralClosure`、`exists_pow_mul_derivAlong_mem`、`derivAlong_mem`、`derivAlong_unit_mul_pow`、`derivAlong_eq_unit_mul_pow_of_aeval`。局部 private helper 已随各模块落地。

固定 Belyi `NoncriticalFinite.lean` 的原始 proof body 正是当前移植链的来源；`Canonical.lean:44` 的有限支撑论证消费同样的有限极点与有限分歧事实。现有 Riemann 维数与逼近定理是共享底层几何基础的旁支消费者，不是有限分歧证明的前提。

已读取既有 MCP-CI 回执 `ci-010859-0314d56f`：状态 `succeeded`、退出码 0，`ClosedFiniteConsumer.lean` 导入一般 `noncriticalRamificationFinite` 并打印其公理，输出只有 `propext`、`Classical.choice`、`Quot.sound`。当前递归导入的 29 个本地模块全部无 `sorry/admit/axiom` 命令，其源码 SHA-256 均与该回执输入记录一致。墙钟 45.1136012 秒；CPU 44.29 秒（user 2.04 + system 42.25）；进程树峰值 RSS 4221898752 bytes；PSS 未知。

`source-closure-static-audit.json` 保存完整 29 模块依赖和 hash 核对；`source-ledger-supplement.json` 保存逐节点来源位置和既有回执摘要。此审计没有启动编译、MCP-CI 或 API，也没有修改主目录或 Git。未对 tmp 组合器新增验收主张。
