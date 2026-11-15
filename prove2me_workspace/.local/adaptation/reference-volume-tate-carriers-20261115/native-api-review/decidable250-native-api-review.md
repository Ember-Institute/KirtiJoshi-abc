对实际 250 个标准依赖及其 Lean 4.33.1 对应项的独立静态检查已完成。

结果文件为 `decidable250-native-api-comparison.json`，可用 `compare_decidable_native_closure.py` 重现。输入绑定源闭包、原生 API 导出和成功查询回执 `ci-013962-60467000` 的 SHA256。该查询由主智能体执行；子智能体没有编译或调用 CI。

250 个名字中有 239 个原生对应项，11 个缺失。存在的对应项有两个 universe 数目差异、两个 kind 差异及七个 typeExpr 语法差异。完整名字和逐项记录均在 JSON 内。

按 v6 唯一精确同名例外 `Nat.decEq.match_1`，实际需要展开的源节点正好五个：`Bool.Reflects`、`Bool.Reflects.match_1`、`Nat.instDecidableCoprime._proof_1`、`Nat.decEq._proof_1`、`Nat.decEq.match_1`。其所有依赖在 14 个保持原生的 API 处停止；它们全部存在，kind、universe 数目、类型 BinderInfo 和 computationShape 相同，typeExpr 经局部名字及 universe 参数 alpha 规范化后逐节点相同。构造器桥另用的 `Decidable`、`Decidable.decide`、`Bool.rec`、`Decidable.isFalse`、`Decidable.isTrue` 的类型也 alpha 语法相同；后两项的 definition→constructor 变化由既定桥接处理。

其余 `Bool.decEq.match_1`、`Decidable.casesOn`/`rec` 和三个 private mod matcher 的差异均不在本次实际源展开路径上。无需据此扩大标准替代范围或增加例外。语法相同不是 kernel 等价证明。

主智能体后续 kernel 验收 `ci-013964-cce30c9e` 已成功，报告 100 个原始选择 = 98 个具名比较 + 两个真实 proof-value resolutions，100 个 owned 声明，标准公理闭包且无 sorry。该独立 kernel 回执及其 SHA256 已附入 JSON；本静态报告不替代它。
