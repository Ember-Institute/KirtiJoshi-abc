# 根智能体归档映射

将本目录整体复制到所选归档目录，所有文件保持逐字节一致。archive-manifest.json 的每行包含相对路径、字节长度和 SHA-256；它不包含自身，避免递归摘要。

copy-map-relative.json 是单独的映射指导：键是记录中的原绝对路径，值是本包内原字节副本的相对路径。根智能体将每个值前置实际归档目录的绝对路径，另存为新的平面 JSON copy-map。不要回写本包的任何原件、元数据或 validation.json。

随后运行归档目录内的 validate.py --copy-map /单独映射文件的绝对路径。验证脚本会从单独 copy-map 解析输入路径，保持工件中的原披露及哈希不变。其余主区、交付模板和 Mathlib 输入可保持原路径；若归档流程另行复制这些输入，根智能体可向单独映射追加它们的原路径与归档路径。

本包中的 source-context/SOURCE_LEDGER.json 是正式台账的完整原字节副本；source-context-references.json 也完整嵌入同一 JSON 对象。不得将 null 对应字段补成同名辅助项，也不得删去 typed collision、compiler-only 或 proof-value evidence。
