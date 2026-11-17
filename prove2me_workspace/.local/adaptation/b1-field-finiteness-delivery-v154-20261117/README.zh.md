两条条件有限性最终交付，持久目录建议为 `prove2me_workspace/.local/adaptation/b1-field-finiteness-delivery-v154-20261117/`。本任务只在 /tmp 写文件，没有调用 CI、API、Git、清理或修改主区。

归档 `b1-field-finiteness-evidence-v154.tar.gz`：467,646 bytes，221 成员，SHA256 `31064565a0fa7c2dd79bc761bfe9bcc821b6cb394b12db743e3a2a9769a98230`。已执行一次压缩并重开逐证据成员验 SHA；外部 gates.complete=true、archiveReopenedSHA256Verified=true。

实际平台结果：torsionCoords theorem `7e6473c2-c415-4617-8f72-6853d7824b06`，publication job `7d59f432-4e2a-4815-bcef-9053ee2c315b`，proof `0191c2d4-6cbc-47bd-b57e-10b71d538f6e`；Extended theorem `55afc5bb-0938-46a4-9088-7aac0f3ced12`，publication job `00b42cf7-29d5-47cc-92b6-ddd9f692ce41`，proof `2ed34fde-fd6a-4d67-b6e3-36819a271d76`。两条 proof 均 ACCEPTED，最终 GET 均 Proved。实际四角色审查核对 source full TYPE/proof、canonical、Sol、exact platform shape、完整 binderInfo 和标准公理。最终第二条仅计 Extended 的代码四项 CI 与四角色 018728，旧四项 Prime CI 仅为历史。

第二 canonical 为 `AbcAdaptation.Tripod.finiteDimensional_fieldOfExtended`；来源数学身份仍为 `Iut.Tripod.finiteDimensional_fieldOf'`。数据 `fieldOf'`、h3/h5 和原 proof 正文保留。原 command 数学字节核对只允许 rename-map 指定 AST declId 绑定范围变化。ASCII 要求来源 `references/upload_full_project.md` 第87行已入档，无 Prime API 失败提交。历史 Prime 模块在原路径删除后，以 CI manifest 的 exact SHA 定位已移动源码，`historical-prime-input-restoration.json` 保存 originalPath→archiveMember；不把旧输入当成当前验收。旧 joint blind 和新的 Extended fresh ASCII readback 均完整保留，后者精确核 canonical codeSHA d58079aa…。

完整原证据包含两实际使用 source full JSON（已逐项与旧 accepted closure 比较）、AST/parser/source ranges、canonical/Sol 原证明、依赖 map、所有叶/产物/four-role 回执和 artifact、原 editorial payload/final frozen shape 与差异、发布/ACCEPTED/Proved、独立三语和论文背景。源 77MB/closure136MB 不重复打包，按 prior references 中 v123/v129 归档 SHA、精确 member 和 member SHA 引用；恢复历史完整来源需同时保留旧归档。1MB nextfacts 未重复打包，未加入下一 mem/gen 单元。

`SOURCE_LEDGER.json`、`ci-history.json`、`prebuilt-pins.json`、`gates.json`、`source-byte-checks.json` 等为紧凑外部记录。`registry.patch.json` 只增加 narrow unit，`plan-addition.txt` 为一行计划更新建议。归档内 gates 为重开验证前阶段；外部最终 gates 保留冻结 SHA。

`cleanup-whitelist.json` 仅允许主智能体验收后删除两个 exact-SHA 已集成 Sol 文件：torsionCoords_finite 与 finiteDimensional_fieldOfExtended。两个 canonical 具名证明、纯数据定义和缓存必须保留。未执行任何清理，不允许其他 Sol 或目录递归删除。

范围仅 `h:TorsionFinite l n` 下坐标有限，以及 `h3:TorsionFinite l 3`、`h5:TorsionFinite l 5` 下生成域有限维。真实消费边为前一定理在后一 proof 中对 h3/h5 的调用；后续 provider 接合保持 pending。不证明实际挠点有限性或无条件 provider 存在性，不关闭 B1 或 S2-04。
