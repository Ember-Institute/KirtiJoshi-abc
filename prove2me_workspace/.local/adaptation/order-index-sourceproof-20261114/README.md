# Order/index source-proof delivery draft

本目录仅包含主智能体后续执行用的脚本和静态审查结果。
本子智能体未调用平台或 MCP-CI，未修改工作区、缓存或 Git 索引。
脚本默认 evidence 目录是：

`/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/order-index-sourceproof-20261114`

发布范围为一个私有 Definition `FermatNoncriticalOrderSource`，以及三个既有 target 的完整证明。
既有 ID 从 `fermat-noncritical-elementary-20261114/published-child-ids.json` 读取。
证明提交顺序为 regular、pole、inverse。
inverse 仅可导入 regular 的既有 theorem 模块。
提交 inverse 前，脚本读取 regular 的实际平台状态和本轮 ACCEPTED 回执。
其他 theorem、自目标、Solutions 和 Open 导入均不允许。

下面是首次发布的原始入口；本轮已完成平台操作，继续步骤见文末。
主智能体验收 compiler 和最终读回后，可在首次发布时执行：

```sh
python3 /tmp/p2m-order-proof-delivery-20261114/platform_publish.py
python3 /tmp/p2m-order-proof-delivery-20261114/finalize.py
```

第一条命令会发布 Definition、验证三份 Solution、同步三 target 的说明和来源。
它还会等待服务器沿既有 accepted sketches 自动传播 Proved。
若两个 composition 祖先实际变为 Proved，它只清理这些节点的过时状态说明。
祖先数学陈述和既有三语审读保持原内容；中文术语仅将“赋值点／赋值位”改为“处”。
[ancestor-metadata.diff](ancestor-metadata.diff) 给出根智能体已审阅的准确差异。
[ancestor-metadata-preview.json](ancestor-metadata-preview.json) 给出完整 PATCH payload。
所有 PATCH 都仅含 `natural_language_statement` 和 `source`。
脚本会检查每个节点的 `formal_statement` 前后逐字相同。

第二条命令验收平台及图回执，然后更新 registry、单元汇总和一个文档。
它只修改 `docs/Prove2Me适配状态.md`：删除三个完成条目整段。
若实际 list-composition 已 Proved，它还移除 P1Minpoly 段落中“复合分歧公式仍未闭合”的失实项。
有限分歧和 noncriticalSelection 的剩余义务保留。
它不修改开发计划、不改勾选框、不修改其他 docs，也不提交或推送。

finalize 只 stage 四个交付模块、所属 Checks、本单元 evidence、registry 和上述文档。
若索引中已有无关路径，脚本会在文档和 registry 写入前停止。
它保留该索引，不 reset、不移除无关暂存文件。

`sourceproof-validation.json` 的准确必需结构如下：

```json
{
  "passed": true,
  "exact_platform_types_equal": true,
  "definition_hashes": {"Definitions/Def_FermatNoncriticalOrderSource.lean": "SHA256"},
  "theorem_hashes": {
    "AbcAdaptation.Tripod.Fermat.Proper.noncriticalPolynomialOrderAtRegularPoint": "SHA256",
    "AbcAdaptation.Tripod.Fermat.Proper.noncriticalPolynomialOrderAtPole": "SHA256",
    "AbcAdaptation.Tripod.Fermat.Proper.noncriticalInverseRamification": "SHA256"
  },
  "solution_hashes": {
    ".local/adaptation/order-index-sourceproof-20261114/Solution_noncriticalPolynomialOrderAtRegularPoint.lean": "SHA256",
    ".local/adaptation/order-index-sourceproof-20261114/Solution_noncriticalPolynomialOrderAtPole.lean": "SHA256",
    ".local/adaptation/order-index-sourceproof-20261114/Solution_noncriticalInverseRamification.lean": "SHA256"
  },
  "declaration_graph_sha256": "SHA256",
  "compiler_checks": [
    {"tag": "receipt-prefix", "source": "workspace-relative-source.lean", "review": false, "artifact": false}
  ]
}
```

`compiler_checks` 必须列出真实的全部验收 gate。
四个交付模块各需 leaf 和 artifact；三份独立 Solution 各需 leaf。
另需声明图提取、`ValidateExistingTypes.lean`、所属 Checks、`AuditAllDefinitions.lean` 和 `ProductionGates.lean`。
每个 tag 对应 `<tag>-request.json`、`<tag>-submit.json`、`<tag>-result.json`。
检查只读取这些已完成 MCP-CI 回执，脚本不会提交新 CI 任务。
review manifest 只核对当前 Definitions/Theorems 哈希。
每份 Solution 由自己的当前文件哈希及独立 receipt 的 `source_sha256` 绑定。

还需以下根智能体验收的输入：

- `decl_graph.jsonl` 和 `existing-types-equal.json`，后者必须为 JSON `true`。
- `final-readbacks.json`，可为 `{"declarations": rows}`，也可为直接数组。
- object 形式应包含 `input_file_sha256`，绑定四个交付模块。
- direct-array 形式需在 validation 中增加 `readbacks_sha256`。
- 每行需有 `declaration`、工作区相对 `path`、`en`、`zh_Hans` 和 `ja`。
- `compiler_name`、`compiler_source_span` 和 `elaboratedType` 若存在，必须与实际图一致。
- private helper 的 `declaration` 保持可读名称；其实际私有名称另存为 `compiler_name`。
- 可选 `readback_names` 字段可将 validation 绑定到准确的六行声明集合。
- `mochizuki-quotation.md`、`source-consumer.json`、`source-ledger-link.json` 和 `integration.json`。
- integration 的 `files` 可为路径数组或路径到哈希的对象，需准确列出四模块及可选所属 Checks。
- 原 root graph/frontier/registry baseline，以及三 target 和两个 ancestor 的 `platform-before-*.json`。

根智能体已保存的 baseline 永远不会覆盖。
首次发布前，`delivery-intent.json` 绑定 validation、读回、引文及来源文件的哈希。
Definition 和 verify POST 前，脚本先保存完整请求和 intent。
有 submit receipt 时，重放会核对原请求，并继续查询原 job/submission。
有 intent 却无 submit receipt 时，脚本停止重复 POST。
主智能体须先恢复原请求的真实受理回执，再以原 tag 继续。
PATCH 使用相同 payload 重放；若响应丢失，准确的服务器读回可核销该次 PATCH。
平台调用失败不能解释为未受理。

图验收比较真实数学节点、依赖对和 reduction 的 parent/children/submission_id。
它允许全体 children 已 Proved 后，既有 sketch 从 SKETCH_ACCEPTED 变成 ACCEPTED。
它允许同一闭包上的祖先从 Open 自动变为 Proved，并记录实际状态。
它不修改相邻节点的状态，也不预设 ancestor 名单的状态必须保持 Open。
root 必须始终未 Proved。
frontier 全部分页，计数和变化来自实际 before/after 回执。
若自动传播尚未完成，脚本做有限次只读查询，再保留原提交供后续继续。

最终汇总保留本目录中全部已终态的 CI 尝试，包括失败尝试。
墙钟、CPU total/user/system 和物理 RSS/PSS 分别记录。
缺失 resource source、degraded、CPU 或内存字段保持 null，表示未知。
源码仅声称保留 copyright、author notices 和 Apache-2.0 release headers；不声称捆绑了上游 LICENSE 全文。

本轮真实 after 图已记录 inverse→regular 的共享数学依赖。
它属于已接受的 inverse proof submission `35b90120-f420-49b4-9557-3e185b3fbce5`。
新增关系两端都是原有且已 Proved 的 theorem；没有新增数学 theorem 节点。
验收只允许这一条新依赖及其 ACCEPTED reduction。
submission ID 必须匹配本轮 inverse 的 verify-result；默认调用还核对 verify-submit。
所有旧 reduction 的 parent、children 和 submission ID 保持原身份。
合法的 SKETCH_ACCEPTED→ACCEPTED 状态升级继续逐项检查。

真实计数为：accepted reductions 18→19，数学 children 56→56，dependency pairs 61→62，frontier 31→28。
finalize 会记录 `added_existing_child_dependency`，不声称数学图结构或依赖边完全不变。
该字段保留 parent/child 的名称、ID、Proved 状态、本轮 ACCEPTED submission ID 及 proof receipt 路径。
registry 的 edges/counts 仍从实际图导出。
不得为隐藏共享依赖而内联证明、删除消费者或重复提交已受理的证明。

当前三 proof、两祖先及 metadata PATCH 都已由根智能体完成。
无需再次执行 publisher 或任何 API 请求。
根智能体可直接从现有回执验收图并保存状态变化：

```sh
PYTHONDONTWRITEBYTECODE=1 python3 - <<'PY_ACCEPT'
import sys
sys.path.insert(0, '/tmp/p2m-order-proof-delivery-20261114')
from delivery_common import IDS_PATH, compare_graphs, read, save
import json
ids = json.loads(IDS_PATH.read_text())
_, after, _, changes = compare_graphs(
    read('root-graph-before.json'), read('root-graph-after.json'), ids,
    read('root-frontier-before.json'), read('root-frontier-after.json'))
save('observed-status-changes.json', changes)
save('added-existing-child-dependency.json', after['added_existing_child_dependency'])
PY_ACCEPT
python3 /tmp/p2m-order-proof-delivery-20261114/finalize.py
```
