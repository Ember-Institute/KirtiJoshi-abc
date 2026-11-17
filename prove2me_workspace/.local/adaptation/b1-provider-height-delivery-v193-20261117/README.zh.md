# Provider4 与条件 localHeightData11 归档准备

仅写本任务临时目录；不调用 CI、编译器、API 或 Git，不执行清理。当前为准备状态，不表示验收通过。

`python3 build_archive.py` 生成预检账本与 member 清单，不压缩。收到父智能体 finalize 信号后，填写 `final-evidence.json` 的终态回执、JSONAssertions 与双私有发布精确 GET，再运行 `python3 build_archive.py --finalize`。归档只生成一次，立即重开并逐 member 验证 SHA256。父智能体随后复制交付物；脚本不写主工作区。

`JSONAssertions` 每项使用 `path`、`member`、`equals`（JSON Pointer → 预期值）。至少分别绑定本轮来源 wholeProp 兼容证书与完整原生对应审查；应检查实际的 TYPE、whole proof、元数据、公理及假设字段，不以 CI 成功替代数学审查。`extraFiles` 补充证书配置、冻结输入和精确 provenance 绑定；每项为 `path`、`member`。`requiredJobs` 中的 `stdoutRequired` 可保存项目门禁的实际公理输出标记。

范围仅为 CurveProviders 四字段接口与 curve selector，以及显式接受 CurveArithmetic/TateInputs 的 localHeightData 十一字段装配。本轮 residueChar 来源 JSON 有 46 条记录，严格记为 1 full proof 与 45 boundary。原生库存有 28 条新 owner 声明，但库存本身不接受对应关系。来源 15 个 Provider/assembly 完整 facts 与已接受 closure 对照，4 条 AST 命令与 normalized/native 字节核对，其中3条与已接受 replay 核对；residueChar 属于原缓存模块，不冒称 replay-owned。

不收入 pending-supplier，不复制旧 77/136MB 来源库。保留既有归档精确 SHA256 引用。P.h 仍应使用真实 localData.height；不将数据接口算作 provider 存在性，TateInputsSupply、后续 P.tate/localData/h 接线、B1 与 S2-04均未完成。旧 torsion-free 证书不可套用于本轮 residueChar；不能把来源 HFQ 与 Free 直接等同。

归档内的 delivery/SOURCE_LEDGER.json、registry.patch.json 与 gates.json 是创建压缩包前的内容；外部同名文件随后仅补充归档 hash 和重开验证结果，以避免自引用。外部 delivery-manifest.json 对最终文件作精确 hash 绑定。

最终发布 payload-final.json 只把 natural_language_statement 的数学显示分隔符改为平台要求的 dollar 格式；原冻结 payload/readback 精确SHA保留。日期上下文为2026-11-18，路径20261117保留本单元起始日期。refer/iut同口径约70%，本单位收口后预计仍约70–71%，不作为父义务完成率。

发布前的第二步仅将 name/title 改为 definition_name/definition_title；api-key-normalization.json 记录全部值不变。payload-before-api-key-normalization.json 是分隔符变换后的中间精确字节；两步分别验证SHA和JSON等值。helper首个KeyError发生在任何HTTP请求前，不登记为POST失败或平台拒绝。
