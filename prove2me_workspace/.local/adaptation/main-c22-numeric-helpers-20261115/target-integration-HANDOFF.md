本批是目标工件及审计草稿，未编译、未运行 CI/API/Git，未修改主区。生成入口：`python3 generate_target_artifacts.py --base <main-c22-numeric-helpers-20261115绝对路径> --out <工件根目录>`。已在本临时目录运行一次生成；可用同一参数重生成。

`Theorems/Thm_*.lean` 七份为目标完整签名加 `by sorry`；`Solutions/Sol_*.lean` 七份仅有一个顶层 `theorem solution`，保留原 proof（含 `:=`）字节。每条 payload 的 preamble/formal_statement/solution 与对应 Lean 文件逐字一致。原版权、Apache LICENSE 和来源 notice 保留。节点粒度是候选集；`log_pi_nonneg` 可由 root 决定保留在现有 consumer 的 inline helper，不要求额外数学节点。

输入直接使用主区七条 actual source compiler types：job `ci-015163-070e492c`，墙钟 148.9483543 秒，CPU 147.71 秒（user 6.78 + system 140.93），峰值 RSS 8,770,723,840 bytes，PSS 未知。生成器绑定该终态回执、原 Expr/keyword 文件、原 source SHA 和完整 whole-AST command/binding/proof 边界。没有新增抽取器，也未要求重跑无项目引用的 RootOnly oracle。

`Audits/Audit_*.lean` 七份分别导入独立 Thm/Sol 工件。复用上一单元 `AuditAssembly.lean` 的封闭性、标准常量 owner、全表达式 BinderInfo inventory、标准公理及依赖闭包门槛，并按 actual source Expr 生成各条 signatureBinderInfo/type category：`log_bound_ell` 4 个，sqrt/half/self 各 2 个，两个 pi 辅助 0 个，sum 为 4 个显式 Nat/Real 参数。审计同时对 source/target/solution 检查该 signature；并执行三组完整 `Kernel.check` + `Kernel.isDefEq`：target/solution、source/target、source/solution。只审计目标 theorem 的类型；solution 禁止直接或传递 `sorryAx`。

所有原标准 Mathlib 常量采用原结构化 Name，不做 source/target 重定位，不新增假设、不用漂亮打印文本重新解析类型。`source-type-constant-inventory.json` 列出每条实际原 type 的常量；目标可用性及语义等价仍待目标 kernel 运行。缺失常量会明确报原 Name，不等价会报 source/target 完整类型，不会伪造接受结果。

主智能体后续把工件置于平台工程根目录，再统一 MCP-CI 编译 Thm/Sol 和各自 audit。Audit 环境：`NUMERIC_ORIGINAL_EXPR_FILE=<B>/source-facts/original-exprs.json`、`NUMERIC_AUDIT_OUTPUT_DIR=<目标审计输出绝对目录>`。`generation-manifest.json` 有每条来源、SHA、生成文件、显式参数规格及 proof/signature 新旧字节映射；`SOURCE_LEDGER.json` 保留真实原 consumers，canonical 接入仍 pending。目标编译、kernel equality、公理审查、canonical 接入均未声称通过。无独立 readback 文件。
