# 初始 theta 四包元数据交付

`blind-readbacks.json` 仅合并两位原审读者的最终 `audit.compiler-reviewed-v2.json`。四个名称字段去除误带的 `Def_` 前缀；全部最终三语正文、逐声明及逐字段说明、歧义、待定术语和其他原始字段逐字保留。

覆盖核对为 19 个声明、7 个结构、77 个字段，以及原审读者复核的 103 条编译器记录。每个上下文的主目标映射恰为两个包，两个映射互不重叠，合集恰为四包。实际安装文件、生成文件、包装报告、`blind-context` 输入及 19 个精确源码命令哈希均已核对。

`author_model` 据 `blind-orchestration.json` 记为 `gpt-6.1-sol`，并明确标注 `author_model_basis: orchestrator_configured`。实际后端未知；两份原件的 `actual_model: null` 原样保留。编译器修订是原上下文的继续复核，不冒充额外独立审读。

`passed: true` 仅覆盖读回字节保存、输入绑定及所供类型复核记录的完成。组装者没有运行编译器、证明验收或新的独立读回，也没有宣称父义务完成。局部组最终修订中，`towerModK` 的塔法则不约束所存 `algebraModK` 的区别完整保留。

- `originals/geometry/` 与 `originals/local/`：两组的原英文、原始 audit、最终编译器复核 audit 和完整修订记录，共 8 个逐字节副本。
- `evidence/`：调度器模型配置和实际形式类型切片的逐字节副本。
- `blind-readbacks.json`：最终交付结构。
- `source-context.json`：独立的论文／代码来源与精确命令范围；不混入盲读回正文。
- `input-manifest.json`：全部输入路径、哈希和归档副本对应。
- `validation.json`、`assemble.py`：一致性结果与组装／只读验证脚本。
- `copy-map-relative.json`：原路径到本包副本相对路径的单独映射。
- `archive-manifest.json`：本目录精确文件清单及哈希，不包含自身。

原样复制本目录后，将 `copy-map-relative.json` 的各个值前置实际归档目录绝对路径，另存平面 JSON 映射；不要回写任何原件或验证哈希。使用 `python3 assemble.py --validate --copy-map /单独映射文件路径` 复核。其他主区、Mathlib、交付模板或来源命令输入保持原路径；根智能体另存这些材料时可向独立 copy-map 补充对应。

全部输出仅在本临时目录；没有主区写入、CI、编译、API、网络或 Git 操作。
