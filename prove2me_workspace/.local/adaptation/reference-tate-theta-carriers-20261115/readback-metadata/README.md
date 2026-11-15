# 四包盲读回元数据交付

`blind-readbacks.json` 已合并两份最终审读原件，覆盖四个定义包。两个独立上下文的主目标映射各含两项、互不重叠、合集恰为四项。28 条原始输入及实际安装文件、生成文件、包装报告和正式台账的哈希检查通过。

本次只组装元数据。`passed: true` 表示离线一致性检查通过，不表示组装者执行了新的独立读回、证明验收或完成了 S2-04。

公式组原件保持不变，另附原审读者的五项形式类型确认。结构组采用同一审读者的 v2，并保留历史 v1、四项 CompleteSpace 假设修订及三项不确定性解除。v2 不计作第二次全新审计。最终原件的三语、覆盖、歧义、proof_notes／optionalproof_notes 及全部披露逐字保留；actual_model: null 和 uniformizer 待定译名保持原样。

来源上下文完整嵌入正式台账，并保存逐字节副本。它保留 78 个来源项（76 个命名常量和 2 个真实证明值）与 77 个当前 owned 项的区别。两个来源证明值的 wrapped、actualCompilerPair 为 null；来源 qOrder._proof_1 的 Infinite (𝓞 F) 与当前同名项的 Module.Finite ℤ (𝓞 F) 类型冲突证据完整保留。组装者没有构造同名身份对应。

- blind-readbacks.json：最终合并数据。
- input-manifest.json：输入、最终／历史原件、英语附件及副本哈希。
- validation.json、validate.py：离线一致性结果与只读验证脚本。
- source-context-references.json、source-context/SOURCE_LEDGER.json：完整来源上下文及台账原字节副本。
- originals/：最终原件、历史结构组 v1、英语附件及公式类型确认的原字节副本。
- review.json：附加元数据记录；组装者未改写原始读回。
- archive-manifest.json：本目录文件的相对路径、字节长度及 SHA-256。
- COPY-MAP.md、copy-map-relative.json：单独的归档路径映射指导。

标题是按实际形式声明编写的编辑元数据，已注明来源。准备阶段记录保留，最终交付以 validation.json 和 archive-manifest.json 为准。主智能体应逐字节复制本目录；不要改写原始披露、已生成工件或其中的验证哈希。归档迁移的路径映射另存，详见 COPY-MAP.md。

全部写入均在本临时目录。未编译、调用 CI／接口／网络、操作 Git 或编辑主工作区。
