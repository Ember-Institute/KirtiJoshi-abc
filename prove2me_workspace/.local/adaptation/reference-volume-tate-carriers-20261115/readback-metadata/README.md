# 新单元盲读回元数据合并包

`blind-readbacks.json` 合并两份已有审读记录，覆盖五个定义包。它包含当前模板和上一单元已接受结构的必需字段。五个规范名称和来源链接来自最终来源台账；实际安装定义、生成定义、包装报告、盲审输入及冻结源码的哈希均已核对。

本次仅执行离线元数据组装。`passed: true` 表示元数据一致性检查通过，不表示本次新增了独立审读或证明验收。原始英文、简体中文、日语、声明覆盖、歧义说明和可选证明说明均逐字保留。

中文沿用用户已确认的“标签集”“标签集递增族”“包络”。NormalizedOrder 原文中的两处 `【待定译名：uniformizer】` 及其他原始待定译名均保持原样。两位审读者对偶然见到的 Mathlib 文档行、前置文件路径修正等披露，也完整保留。`author_model` 是原始任务指定标签；原始 `actual_model: null` 没有被改成猜测的运行时身份。

Tate v2 由同一审读者在继续的上下文中核对更新后的 Weierstrass 文件，并非第二次全新审读。它的三包内容与 v1 完全一致。v1 原件及输入清单作为历史记录保留；只有 v2 的当前输入哈希用于绑定现有包装文件。

LogVolume 的 `source` 精确沿用最终台账的完整上游文件链接。有效源码行号独立保存在 `source-context-references.json` 中，没有被误装成上游行号。

- `blind-readbacks.json`：最终合并数据，含两个原始审读上下文的明确归属。
- `input-manifest.json`：两份最终原件、一份历史原件、24 条原始输入的核对结果，以及台账、包装和源码哈希。
- `review.json`：附加元数据记录；没有翻译更正或原文编辑。
- `source-context-references.json`：独立的来源、有效／上游源码及台账引用记录。
- `validation.json`：离线一致性检查及交付文件哈希。
- `originals/`：最终两份原件和历史 Tate v1 的逐字节副本。
- `assemble.py`、`validate.py`：组装与只读验证脚本。运行 `python3 validate.py` 可复核当前输入和交付文件。

三语标题是按实际形式声明编写的编辑元数据，已注明来源。标题中的“附正整数”不把任意的 `orderNat` 附加数据称作内在乘法阶。

`prepared-wrapper-validation.json` 和 `required-delivery-schema.json` 是准备阶段记录；最终交付以 `validation.json` 为准。所有输出均在本临时目录；没有编译、调用 CI／接口／网络、操作 Git 或编辑主工作区。

主智能体迁移文件时可更新组装副本路径等新增元数据；`original_metadata_verbatim`、`original_provenance_verbatim` 等原始披露内容须保持原样，其中的历史临时路径由新增档案映射补充说明。
