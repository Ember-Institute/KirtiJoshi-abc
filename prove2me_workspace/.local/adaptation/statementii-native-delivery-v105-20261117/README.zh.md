已完成的独立证据包，供主智能体在活动独占 CI 终态后复制与登记；本任务未执行 CI、API、Git 或主区写入。

将本目录交付文件复制到 `prove2me_workspace/.local/adaptation/statementii-native-delivery-v105-20261117/`。归档为 `statementii-closed-native-evidence-v105.tar.gz`，2,796,949 bytes，SHA256 `0946bae79c53b2018bc704d578e10e36a623310c66915f4e96000e3257974e12`。已逐一读回并校验全部 59 个证据成员的 SHA256，另含内部 content manifest，共 60 成员。无 B1 未完成草稿。

`SOURCE_LEDGER.json` 与 `ci-history.json` 以 archive member SHA256 和 JSON pointer 引用完整事实，不重复大型 Expr/配置 blob。`registry.patch.json` 是单个 add-only JSON Patch；将其 value 添加到 `/reference_source_preparation/statementii_closed_native_portable_bridge_unit`。不得覆盖 registry 当前其他字段。`plan.patch` 只在原来源提取条目后加入一个独立完成条目，保留规范接合和 S2-04 的开放 checkbox。历史 v93 source-only 记录保持当时状态；新 v105 单元记录后来闭合形式桥的实际目标验收。

成功回执 `ci-018506-8f6104c5` 已核对：exclusive_worktree、snapshot_id=null、实际 source hash、退出码 0、review passed、完整 TYPE/proof 内核检查及标准三公理。wall 78.9903235s，CPU 79.29s（user 10.4s + system 68.89s），峰值物理 RSS 5,170,802,688 bytes；PSS 未知。失败回执 `ci-018491-d9ab417b` 和原 query 均保留。失败到最终 source 的精确比较表明，除名称 lookup、两处 do 与公理打印外无变化；旧 relocation 算法和完整 proof/data/aux 审查门未改。

`actual-difference-summary.json` 的五项报告指向归档内完整 raw diff。根完整 TYPE/proof 的 raw alpha 结构均不同；只展开具名 RHS 后 TYPE 的 binderInfo/path 一致，但三处表达式差异仍保留。aux1/aux3 TYPE 与 proof exact 相同；aux2 TYPE/proof 各有三处 raw 差异，分别是 `toCommSemiring`/`toDivisionSemiring`、`CommSemiring`/`DivisionSemiring` 和 binder 名 `l`/`z`。根 proof 的 52 项差异路径完整保留。内核等价不被记为完整 proof 树逐字一致。

归档中的 `readback/` 是独立 gpt-6.1-sol 盲读原件，inputhash `a715289c96cfdd00043c2aba1cf78b0555821f010e0ab3434a684a29309b9a8c`；冻结 English 字节及全部读回输入 SHA 已核对。`citation/separate-context.json` 单独保留 Mochizuki Theorem 2.1(ii)、印刷 p.11 / PDF p.11 的原 quote 与既有视觉核验来源，未回填或改写盲读，也不把等价桥称为论文新定理。中文 compactly bounded 术语维持待定占位。

来源实际消费边为 root1/三个辅助 → 来源 root2；目标实际消费者为 CI-only replay root 及其 CI full audit。`AbcAdaptation.Tripod.statementII` 仅为待接合生产消费者，未记为已经消费。本包不发布平台节点、不修改生产 root、不关闭 canonical C22 或 S2-04。
