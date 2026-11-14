# LogVolume v3 独立静态审查

结论：当前补丁保持 componentVol_prime_preimage 的数学含义，不增加结构字段、实例假设或公理。建议以当前补丁接受主智能体已提交的 MCP-CI 检查；本审查没有编译，不能宣称通过。

审查输入：source-project/Iut/Cor312/LogVolume.lean，SHA256 `002f44da071e858c1fe48f3608da4e75f1179d3cd6c3007444bc5453440b7ef0`。已将精确输入只读复制到本目录 LogVolume.lean；LogVolume.patch 是相对于已存档 v2 的最小差异。本任务未修改主工作区、参考源或缓存，也未调用 MCP-CI/API。

## 已核对的首错与连锁错误

- v1 job ci-012585-d85afa5c 和 v2 job ci-012597-057555f9 的首错相同：字段中 IsUnit 缺少 Monoid、未定 cast 的乘法尝试 HMul ℕ Summand、两个点式缩放缺少 HSMul Summand (Set Summand)。
- 之后 LogVolumeData 未定义及 Fintype/Zero/vol.weight 等错误，均位于失败的结构声明之后，应先作为连锁错误处理，不需要逐一改后续定理。
- v2 恢复 relaxedAutoImplicit=false 与 maxSynthPendingDepth=3 后首错不变。不能把配置遗漏直接称为根因；实例合成失败的精确归因仍未确定。

## 当前 v3 修改的静态判断

1. 在原有 i、p、c 全称量化之后，字段内部 letI 把 CommRing 实例直接设为 `(D.packet i (.finite p)).ring_summand c`。这是原 DirectSumPresentation 自带字段的投影，是定义出来的局部值，不是新的全称实例参数，也不是新增结构字段。letI 仅作用于本字段余下的命题。
2. 使用的环结构与原设计应由全局实例搜索获得的 ring_summand 相同；按 let 的定义归约，环运算、单位及自然数嵌入仍来自同一个结构。没有改成 Field、没有加入 IsDomain/Nontrivial，也没有缩小 a 的范围。
3. lambda 形参 x 和自然数 p 的最终 cast 均明确写为相同的 Summand。这给乘法确定输入与输出载体；原源中的 `_` 曾允许 cast 先被解释成 ℕ，回执的 HMul ℕ Summand 是其直接表现。显式标注表达的是原文“在该 summand 中乘以 p”，不改变数学运算。
4. IsUnit a 条件、区域 a • integral c、乘法映射的逆像、componentVol 的等式和右端加 Real.log p 均保留，等式方向未变。没有把取逆像改成取像，也没有把加 log p 改成减 log p。
5. 文件仍 `open scoped Pointwise`；当前 Mathlib 的 Set.smulSet 正是此 scope 中的实例，由 SMul Summand Summand 派生对集合的缩放。Lean 4.35 Init 的乘法到自身 SMul 实例也在。局部 CommRing 应提供所需 Mul/Monoid/NatCast；这一步是否实际成功由主 CI 回执确认。

## compiled type 与源的已知对应关系

缓存 decl_graph_cached32.jsonl 实际由 4.35.0-rc3 提取，不应由文件名误判成旧编译器 ABI。其 ring_summand 行为：

```
{C : Type u} → (self : Iut.DirectSumPresentation C) → (c : C) →
  CommRing (self.Summand c)
isInstance = true; axioms = []
```

源 PacketPresentation.lean 第 68 行同样声明 `[ring_summand : ∀ c, CommRing (Summand c)]`，第 77 行重新标记 instance。当前源与缓存图在此返回类型上没有发现差异。它不是 Field，修复也没有假定 Field。

当前 /home/admin-wsl/Coq/mathlib4/lean-toolchain 是 4.35.0-rc3；Mathlib/Algebra/Ring/Defs.lean 的 CommRing extends Ring, CommMonoid；Ring extends Semiring；Semiring.toMonoid 明确标为 instance。Lean 4.35 Init 提供 Mul 到自身 SMul。Set.smulSet 为 Pointwise scope 的 SMul α (Set β) 实例。没有证据表明需要替换 CommRing 层次或重建 Mathlib。

缓存图的 elaboratedType 使用 pretty printer，未保留所有显式隐式参数和完整表达式；仅凭该图与静态源无法证明编译器内部候选树/透明度行为完全一致。因此目前确认的是“已有环投影，字段内显式应用它并确定 cast”，不能把成功（若后续通过）反推为已查明底层实例搜索的唯一根因。

## 验收边界

本次补丁只修一个参考叶模块的 elaboration。主智能体需读取当前 v3 的实际 CI 终态、参数、诊断，并按其工作流继续后继参考模块；本报告不将未运行检查计作通过，也不宣称整个参考项目或数学父义务已完成。
