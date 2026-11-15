交付目录：`/tmp/p2m-main-numeric-delivery-v6-20261115`。只写临时目录；无 API、CI、编译、Git 或主区修改。

`delivery.py` 是最小 shim：导入旧 `main-c22-numeric-reference-split-20261115/delivery.py`，替换数值单元、候选名字、离线 prepare 和额外证据 preflight。旧脚本的网络实现、私有 mission/owner/env GET、POST intent/receipt 幂等日志、PUBLISHED/ACCEPTED 轮询、读回以及 root graph 前后逐字相等检查直接复用。旧摘要字段 `both_direct_proofs` 是继承的历史名称；本批实际每个 selection 都经过同一 ACCEPTED 循环。

离线运行已成功：`python3 delivery.py --out <review目录>`。默认六个候选，排除 `log_pi_nonneg`；`--names <完整名...>` 可选六个中的子集。没有发布。`review-packet/packet.json` 是可复核实际候选 payload；`ready.template.json` 的 passed 和所有 gates 均为 false，脚本不生成 ready=true。不要把模板直接当作可发布批准。

prepare 消费实际 `B/generated-target/{SOURCE_LEDGER.json,generation-manifest.json,payloads}`、原七 actual source types/source facts receipt、七 actual kernel audit JSON、35 actual 编译/审查回执、主智能体的 `B/blind-readbacks.json` 与 unmodified originals/metadata。复验 original source SHA 和七个原 proof 字节区间，目标 proof 字节精确相同。blind formal 输入仅比实际目标删去固定 327 字节版权/适配注释，余下逐字相同；不改写读回文字，actual_backend 保留 null。没有新建同义 readback 汇总。

英文 paper source context 与 unchanged formal-blind readback 分栏。引用现有 mainbound `paper-materials-v1/quotations-and-evidence.json` 的真实 IUT IV Step (v)/(vii) 引文和页图/原文本 SHA。全部 18 条引文材料以文件 SHA 绑定，但只展示相关的两项背景；明确本批是工程数值辅助，并非原文逐字定理，也不构造 initial theta data。原精确 reference 源代码/commit/行链接保留。

`required-evidence.template.json` 给主智能体最后填写：ProductionGates 成功回执（ci-013203-76bab44a 或 ci-014934-*）的原 `input_hashes` 和 `configuration_hashes` 必须全部重哈希不变；新 git diff --check exit 0 记录须绑定 packet 的全部14源码 SHA；existing readonly mission scope 记录须以 SHA 绑定。35实际回执、7kernel、14leaf、14artifact 与 source/原proof/readback metadata 都是必需项，不能仅用六个发布项的窄检查替代。旧 preflight 继续检查实际 arguments、源 SHA、exclusive/null-snapshot、review passed、≤16GiB 和全部证据 SHA。

安装：主智能体可按 `install-manifest.json` 只复制 shim 到 `B/delivery.py`，再从实际 B 调用 prepare 生成新 packet/模板。脚本仍引用旧 delivery.py；该依赖 SHA 也进 packet。无需复制临时 review packet。主智能体完成必需证据后自行生成最终 ready，显式调用 `deliver(packet_path, ready_path, platform_directory)`；本交付不调用 API。

成功交付后，`registry_candidate(registry_path, platform_directory, output)` 仅写离线候选：只扩 `reference_source_preparation.proved_nodes` 和其新的 `numeric_helpers_unit`。所有旧 units、其他 registry 字段及 root graph counts 保持原样，canonicalC22Connected=false。`log_pi_nonneg` 仅记录为 theorem110 原消费者 inline helper，不进 published/proved 列表；subset 中其余未发布项也保留为 source helper。函数要求真实 delivery-summary、每条 ACCEPTED 和 private published GET 证据，不在当前阶段伪造平台 ID。最终 registry 文件仍由主智能体审查/安装。
