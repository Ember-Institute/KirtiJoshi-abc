# 项目智能体工作约定

本文件适用于整个仓库。编译纪律汇总自 `docs/开发计划.V1Act1Scene1.md`、
`docs/具有明确参考来源指示的证明义务.md`、`docs/Scene1进度总览3.md`，以及
MCP-CI、worktree-isolation、subagent-workspace 技能。本文件统一后续编译流程；
历史记录中的手动 CPU affinity、线程数、并行度和内存限制命令不再作为执行要求。

## 所有编译通过 MCP-CI

- Lean、Agda、Coq/Rocq 的叶模块、检查、审查和全量编译一律交给 MCP-CI。
  不在 shell 中直接启动 `lean`、`lake build`、`agda`、`coqc` 或 `dune build`，
  也不在 MCP 工具不可用时绕过调度器自行编译。
- 编译进程、CPU 并行度、affinity、超时、物理内存监控和 Worker 生命周期由调度器管理。
  不传任意 shell 命令、`taskset`、`-j`、CPU mask、线程数覆盖、硬内存限制或调度超时覆盖。
- 复用现有热缓存，保持 Lean 工具链与依赖锁定；不删除 `.lake/build`，不主动冷建 Mathlib，
  不为一次叶检查重新下载或重建依赖。确实缺少依赖产物时，单独提交所需依赖构建。
- 允许读取 Git 状态、工具链、依赖清单与构建环境。`lake env printenv LEAN_PATH`
  用于读取搜索路径，须在 `ArithmeticTeichmullerSpaces/` 项目目录执行；
  只提取其 stdout 中的路径值，不把 warning、stderr 或换行混入 `LEAN_PATH`。

## 叶模块首次编译与后续估计

- 每个叶模块的首次编译，固定填写 `expected_duration: "60s"` 和
  `expected_memory: "16GiB"`。即使认为首次会更慢或占用更少，也不提前调整这两个值。
- 首次失败后的第二次编译开始，才根据失败原因、实测墙钟时间、峰值 RSS/PSS、
  同类模块和此次改动进行实际估计。超时只提供耗时下界，不能把超时时长当成完整编译耗时。
  已有编译历史的同一模块不因换会话或重试而重新算作首次编译；成功后的复验沿用实测依据。
- 这些字段是资源预估，不是硬限制。当前调度器的叶任务超时为预估时长的三倍，
  因此首次 `60s` 对应 `180s` 编译超时；实际规则以调度器回执为准。
- 叶模块单独编译的进程树峰值 RSS 超过 16 GiB 时，必须拆成更小的声明或叶模块，
  分别验收至 16 GiB 以下。不得通过提高资源申请、删减目标陈述或丢失证明链代替拆分。
- 工具传输失败不等于首次编译失败。先查原任务状态，不据此创建新的编译尝试。

## 目标、工作区与独占模式

- Lean 叶检查使用 `task_type: "leaf"`、`target: "file"` 和准确的 `parameters.source`。
  通过结构化 `environment.LEAN_PATH` 提供现有依赖搜索路径，直接检查该源文件。
  不把叶检查擅自改为 `lake build <模块>` 或全图构建。
- 本会话主工作区为 `/home/admin-wsl/Coq/prove-abc`。主智能体执行独占任务时，直接提交
  当前工作区绝对路径，设置 `exclusive: true`；不用为了规避快照而另建 worktree 或复制整份缓存。
  此时回执应为 `workspace_mode: "exclusive_worktree"`、`snapshot_id: null`。
- 独占只保证 MCP-CI 内部调度互斥。提交后到终态前，所有协作者必须保持该任务的源文件、
  依赖和缓存输入稳定，不编辑、清理或并发构建这些输入。
- 其他会话使用各自登记的 worktree；子智能体草稿放在任务专属临时目录，
  不修改其他会话工作区。共享或需继续修改的输入使用普通快照任务，子智能体默认使用快照。
- 快照任务填写 `snapshot_inputs`，完整列出目标、传递依赖、构建配置、依赖锁与必要产物；
  提交后活动目录的修改不得被当作该快照任务的输入。注意迁移目录后相对依赖路径仍须有效。
- 审查使用 `task_type: "review"`；确需全量验收时使用 `task_type: "full"` 和正确构建目标。
  全量编译独占启动并直接使用稳定的工作区；不另建项目级全局锁。

## 提交、等待与故障处理

- 请求必须包含语言、项目、绝对 `workspace`、任务类型、目标、结构化参数、资源预估、
  `session_id`、`agent_id`、`worktree_manifest` 和 `idempotency_key`。
  manifest 记录实际 `worktree_id`、HEAD、修改文件、未跟踪文件、工具链、依赖锁，
  以及任务需要的目录外依赖与预构建产物；不得将脏工作区申报为干净提交。
- 提交后立即保存 `job_id`。同一请求因回执不明而重放时使用原幂等键；
  修改源文件、参数或资源预估后产生的新尝试使用新幂等键，避免取回旧任务。
- 用 `ci_status` 查询状态，用 `ci_wait` 等待；明确传 `timeout_seconds`，
  小于 MCP 客户端单次工具超时，并为传输留出余量。非终态返回后继续等待同一 job，避免高频轮询。
- `Transport closed` 或 MCP 调用超时不能证明任务未受理、编译失败或 daemon 不存在。
  查询原 job；未拿到 job ID 时用原幂等键重放，核对是否去重，不盲目重复编译。
- MCP 通道异常时先检查代理、daemon 的协议 ping 和任务状态。进程存在并不等于协议健康。
  必要时通过新 stdio 代理或 daemon 协议访问同一个调度器，保持编译仍由 MCP-CI 管理。
- 取消使用 `ci_cancel`，不直接杀编译器子进程。daemon 重启使用受控接口，
  必须由调度器确认没有活动编译；不能因读取超时直接杀 daemon 或启动第二个数据库 owner。
- 分别处理 `failed`、`timeout`、`oom_killed`、`cancelled`、`interrupted`、
  `scheduler_error`。`running`、`queued`、`preparing_snapshot` 均不算通过。

## 回执与项目验收

- 终态后读取 `ci_result`，必要时读取 `ci_logs`；核对 workspace、源文件、
  `actual_arguments`、独占/快照模式、退出码、诊断和资源数据，再报告成功。
- CPU 总时间读取 `resources.cpu_time_seconds`，同时保留 `cpu_user_seconds` 和
  `cpu_system_seconds` 明细，核对总量为两者之和。墙钟时间单独报告；缺失值写作未知，不能当成 0。
- 内存使用进程树物理 RSS/PSS，区分 bytes、GiB 与十进制 GB；不把虚拟地址空间、
  commit 或 pagefile 使用量当作物理内存超限。记录资源来源及 degraded 标记。
- 每个逻辑单元交付前必须通过新叶模块、所属 Checks/Axioms、ImportAudit、
  Act1Scene1 聚合、AxiomAudit 和 `git diff --check`。这些编译/审查仍通过 MCP-CI；
  检查通过后不无故重复全量构建。提交推送按当前任务的授权执行。
- Lean 审查须检查 `sorryAx` 和公理输出；不得把只有编译成功当成公理审查通过。
  新定理公理应仅含项目允许的 Lean 标准公理，并记录异常。Agda/Coq 审查对应检查安全选项与假设依赖。
- 每次失败、优化、重试与最终验收记录对应 job ID、输入版本、退出原因、墙钟/CPU 时间、
  峰值物理内存及诊断。窄目标通过只覆盖这些目标，不能宣称整个项目或数学父义务已完成。

## 证明性能与导入纪律

- Mathlib 只精确导入实际需要的模块。Scene1 禁止导入 `Prologue/Obligations`、
  Scene2、Act2 或隐藏全局输入以补齐未完成证明。
- `maxHeartbeats` 首次失败后先做显然可行的优化，定位昂贵 tactic；必要时用 `show_term`
  查看证明项，测量消耗并改为更直接的证明项。所有诊断编译同样交给 MCP-CI。
- 优化后仍需提高 heartbeat 时，按 `1_000_000`、`2_000_000`、`4_000_000` 顺序有限尝试；
  仍不通过或无法降低开销则拆分小引理，不无限翻倍，也不全文件设置无限 heartbeat。
  交付时须回到默认值，或完成充分细的小引理链并将提高值限制于单个声明或局部实例化。
- 每个 producer 输出必须有实际消费者，消费者字段可追溯到 `SOURCE_LEDGER.md` 的来源与忠实度。
  不通过重命名、删除义务字段、降低目标陈述或引入额外未审计假设来制造通过。
