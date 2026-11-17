参数成员证明与纯 generator 数据交付。持久目录建议为 `prove2me_workspace/.local/adaptation/b1-curveof-generator-delivery-v161-20261117/`。本子任务只写本 /tmp 目录，没有调用 CI/API/Git/编译或修改主区，未执行清理。

归档 `b1-curveof-generator-evidence-v161.tar.gz`：1,290,180 bytes，206 成员，SHA256 `c53435280cca41cefa946d00e528bb296a0a5399def056e30c25336a557a075d`。已执行一次压缩、重开逐成员及归档内 manifest 验 SHA；外部 gates.complete=true、archiveReopenedSHA256Verified=true。归档内 gates 保留重开前阶段；外部最终 gates 保存冻结归档 SHA。

实际平台：成员 theorem `3869aaba-645c-4f11-a327-b50291cc2879`，publish job `1331c803-a696-40bf-84e7-b5dc63814f02`，proof `a11bcc46-f03f-430c-a9b4-e1bcd794f6d3`，最终 ACCEPTED / Proved / private。definition `df14b784-2e17-4f80-a69b-47b96ebf62c9`，发布 job `c5f5c8ce-2f1c-4b5f-83aa-4c1818ed81e4`，PUBLISHED / private / 全提交字段精确回读。历史 theorem/published-item.json 的 Open 仅是发布后初态；最终状态以 theorem/proved-readback.json 为准。definition publishjob 通过通用 theorem_id 字段提供定义 ID；root 首次客户端读取 KeyError 后修正字段并 GET，没有失败 API、没有重 POST、没有数学 payload 改动，两个版本的 root helper 和说明均保留。

四角色加 gen 最终审查 `ci-018802-15b04e72` 通过：source 为两完整 original records，reports 包含 canonical、global Sol、精确平台形状、纯 gen；核对完整 TYPE/value、严格 binderInfo、标准公理且无 sorryAx。两次失败 `ci-018798-635a9b4a`（保留 token meta）和 `ci-018801-b954c4bc`（ByteArray.all 不可用）的实际输入均按 CI exact SHA 保存，restoration map 记录原路径到历史成员；重试只修客户端审查 query，没有改数学代码。共保留10项实际 CI 回执及对应请求、提交、artifact、实际输入版本和资源。最终 mandatory `ci-018804-1111c066` 成功导入 Checks、ImportAudit、Act1Scene1、AxiomAudit 缓存并打印／检查三个新节点仅含 [propext, Classical.choice, Quot.sound]；wall 123.3549196s、CPU 122.52s（user5.6+system116.92）、物理进程树 RSS 8,509,415,424 bytes（约7.93 GiB），PSS 未知。

完整证据包括 source full TYPE/value、原 AST/source 命令与三处绑定标识改名、canonical/Sol/gen 源码、实际依赖与消费者边、独立冻结英文和中日译文、论文原始引用、editorial payload 与最终 API/验证回读。源 77MB/closure136MB 不重复打包，按 prior-archive-references.json 的既有 archive/member/SHA 引用；完整恢复需保留 prior archives。没有宣称 source/native proof term 字节相同。

SOURCE_LEDGER.json、ci-history.json、prebuilt-pins.json、gates.json、source-byte-checks.json、historical-ci-input-restoration.json 为紧凑外部记录。registry.patch.json 仅增加此窄单元，plan-addition.txt 为计划记录建议。root 可将本目录完整复制到建议持久目录后应用这两份记录；本子任务未执行复制或主区写入。

cleanup-whitelist.json 只列一个允许主智能体验收后删除的已集成 Sol：`/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Sol_AbcAdaptation_Tripod_mem_fieldOfExtended_self.lean`，exact SHA256 `cb433a7f19159f4e1ef974f4237b9b73a950f8481fdc53b963eb795c8094c3ba`。cleanup_exact_solution.py 默认模式已核验源 SHA、归档恢复源和 mustKeep，cleanupPerformed=false；root 接受后才可在持久目录运行 `python3 cleanup_exact_solution.py --apply`。canonical 具名证明、gen 定义、其他 Sol、所有缓存必须保留，无目录递归删除许可。

范围只为所有 l:Qbar 的 l∈fieldOf' l 和 gen' l=⟨l,成员证书⟩。canonical 成员证明已被纯 gen 实际消费；源 gen' 的 curveOf/genC 等消费者保留为真实来源边，后续目标消费者仍 pending。不宣称 l 单独生成整个域，不证明实际挠点有限性或无条件 provider 存在性，不关闭 B1 或 S2-04。
