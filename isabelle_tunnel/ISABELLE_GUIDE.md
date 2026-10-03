# Isabelle 主线：控制协议的形式化验证

## 项目定位

重点是用 Isabelle/HOL 建模、定义性质、构造证明与反例，不要求转成硬件制作。工程对象是一个明确写出的共享资源控制协议；形式化方法是项目的核心手段。

这份记录描述实际检查过的内容，不承诺职业评估结果，也不把工具生成的内容自动归为用户独立完成的工作。

## 本次正式检查

- 日期：2026-10-02（Australia/Brisbane）。
- 工具：Isabelle2025-2。
- 会话：`Tunnel_Knowledge`。
- 结果：`Finished Tunnel_Knowledge`，退出码 0。
- 本次运行：会话约 4 秒，总计约 8 秒；不作为性能基准。
- 新增证明没有使用 `sorry` 或新增公理。
- 证明依赖 Isabelle/HOL 与其标准库；固定点循环的底层终止性结论复用 `HOL-Library.While_Combinator`，不是重新发明标准库证明。

## 文件与已验证内容

| 文件 | 内容 |
|---|---|
| `Tunnel_Knowledge.thy` | 协议动作、可达状态、不变量、互斥、知识性质及错误授权的碰撞反例 |
| `Finite_CTLK.thy` | 有限状态域、公式语法、集合语义、固定点迭代及检查器正确性 |
| `Tunnel_CTLK.thy` | 隧道模型的有限性、通用模型实例、公式衔接、无限执行安全性和活性反例 |
| `Tunnel_Liveness.thy` | 强转移公平性、等待状态的通行路径、最终进入及安全服务定理 |
| `Round_Robin.thy` | 具体交替调度器、原协议精化、全程安全与紧的八槽通行上界 |
| `Delayed_Controller.thy` | 外部计数请求、分阶段完成确认、安全不变量与响应条件下的最终服务 |
| `check_model.py` | 独立状态枚举交叉检查；不是经过认证的代码导出 |

### 通用检查器

`formula` 支持原子、否定、合取、EX（构造子名为 `Next`）、EU、AF、个体知识、群体共同知道、分布式知识以及共同知识。

- `iteration_terminates`：若算子单调且保持有限状态域，则从空集启动的固定点循环返回结果。
- `iteration_correct`：该循环结果等于最小固定点。
- `checker_correct`：对于每个该语法中的公式，集合级检查器结果等于文件中定义的语义。
- 另有知识的真实性、正内省、负内省及群体算子的展开性质。

重要边界：EU、AF 在此使用最小固定点语义；共同知识使用反例状态的关系传播。当前没有完成这些定义与书中整套路径语义和迭代知识语义的通用等价证明。检查器使用 HOL 集合，并未导出为独立可执行程序；没有验证 OBDD 或 SAT 后端。

### 隧道与检查器的衔接

- `encode_injective`、`finite_states`：把状态映射到两车位置与许可的有限元组，证明状态域有限。
- `meaning_know_bridge`：原案例的知识定义与通用模型中的 `Know` 对接。
- `chapter8_3_checked`：在当前模型中，公式 `AG(In_i → K_i ¬In_j)` 的检查器结果包含每个可达状态，其中 i、j 是不同列车。
- `safety_formula_checked`：`AG(¬Collision)` 的检查器结果包含每个可达状态。
- `infinite_path_safety`、`infinite_path_knowledge`：直接对 `nat → state` 无限执行证明上述安全与知识性质，不只是引用固定点定义。

这里的 `Globally p` 定义为 `¬E(True U ¬p)`。这些实例化结论不等于已经形式化整章理论。

### 活性：明确证明做不到的部分

- `waiting_forever_counterexample`：存在一个可达等待状态及合法无限执行，列车始终等待。
- `af_cannot_force_progress`：由于每个状态都有空转自环，当前不带公平性限制的模型中，`AF p` 的真值集合恰好等于 p 的真值集合。
- `eventual_entry_not_guaranteed`：列车 A 请求进入后的状态不满足 `AF In_A`。

含义不是“安全证明错了”，而是“不碰撞”与“最终得到服务”是不同要求。不能为了让后者成立，悄悄删掉空转或把想证明的结论写成假设。

## 建议阅读顺序

1. 先看 `step` 与 `invariant`，解释每条动作为什么保持不变量。
2. 看碰撞路径，理解未释放许可与当前占用的区别。
3. 看 `knows` 与 `meaning_know_bridge`，理解观察信息限制。
4. 看 `checker_correct` 和有限固定点循环，区分算法证明与具体公式证明。
5. 看无限等待反例，再决定需要哪一种调度假设或新控制策略。

在 Isabelle/jEdit 打开 `Tunnel_CTLK.thy` 可沿导入关系阅读三个理论文件。命令行复现见 README。

## 后续有意义的证明任务

尚未完成：完整路径语义对应、共同知识的迭代语义对应、硬件或并发程序与抽象模型的精化对应。具体离散调度器已在 `Round_Robin.thy` 中定义并证明通行上界，但未将其导出部署，也未声明其满足先前的强转移公平条件。OBDD、SAT 编码、实时逻辑和部分序约简属于另外的技术分支，不能算作已经检查。

强转移公平下的最终通行已完成，见下一节。随后完成的具体轮流调度器不依赖这项假设，直接证明了有界通行，见 [ROUND_ROBIN.md](ROUND_ROBIN.md)。

再后续的外部请求与延迟确认模型见 [DELAYED_CONTROLLER.md](DELAYED_CONTROLLER.md)。该模型的队列计数无上限，活性证明使用进展度量与自然数归纳，不是有限状态枚举；它目前没有数值等待上界。

其上新增的编号确认层见 [NUMBERED_CONTROLLER.md](NUMBERED_CONTROLLER.md)，已证明到延迟控制器的精化、旧轮次确认拒绝，以及原始报文响应条件下的最终服务。这是两个抽象模型间的精化，不是硬件或并发程序的实现验证；确认真实性、重启和编号回绕仍在边界之外。

后续的设备与保留状态重启模型见 [PHYSICAL_RECOVERY.md](PHYSICAL_RECOVERY.md)。已证明明确设备与可信来源规则下的实际占用互斥、旧会话确认拒绝、合作恢复的逐步安全与最终服务，并有绕过来源和丢失检查点的形式反例。抽象恢复规则尚未对应具体密码、存储或硬件实现；有限编号回绕也未覆盖。

有限编号范围与耗尽锁定、抽象双槽检查点和检查点集成反例现已另行完成，见 [BOUNDED_CHECKPOINTS.md](BOUNDED_CHECKPOINTS.md)。它们证明锁定保持安全，但不保证锁定后服务；证明检查点恢复完整，但不保证载荷足够新。提交与设备动作的联动仍是下一项独立义务。

上述联动义务现已推进到独立的准入核心，见 [DURABLE_ADMISSION.md](DURABLE_ADMISSION.md)。`Durable_Admission.thy` 证明已提交许可覆盖实际占用与在途命令，以及跨崩溃的互斥安全；完整构建已通过。它仍使用真实、原子检查的清场条件，尚未以具体消息握手实现该条件，也没有宣称完整编号控制器已具备持久化实现。

后续 `Fenced_Handoff.thy` 已将清场条件落实为显式异步消息协议，并通过完整构建，见 [FENCED_HANDOFF.md](FENCED_HANDOFF.md)。建议依次阅读 `fence_step`、`fence_core`、`acknowledgements_establish_quiescence`、`fence_step_valid`、`received_handshake_meets_admission_guard` 与设备门槛丢失反例。新的证明仍依赖设备门槛不回退、本地执行检查及可信确认来源，尚未对应实际固件和认证实现。

新增 `Endpoint_Persistence.thy` 已将设备门槛持久化与掉电恢复纳入模型，见 [ENDPOINT_PERSISTENCE.md](ENDPOINT_PERSISTENCE.md)。建议阅读 `endpoint_step`、`endpoint_valid`、`acknowledged_floor_is_durable`、`endpoint_finite_run_refines_fencing` 及提前确认碰撞反例。完整构建已通过；这是到消息协议的有限执行精化，仍不是实际存储和固件实现验证。

后续 `Endpoint_Activation.thy` 已分离存储提交与内存启用，见 [ENDPOINT_ACTIVATION.md](ENDPOINT_ACTIVATION.md)。建议阅读 `activation_valid`、`StoreCommit` 与 `ApplyFloor` 的规则、`split_commit_activation_safe`、`committed_gap_still_uses_old_gate` 和 `disk_only_acknowledgement_can_collide`。完整构建与十组独立测试通过；新层到消息协议有有限执行精化，但不要求间隙状态满足上一层的门槛相等条件。

新增有限轮次集成见 [FINITE_ACTIVATION.md](FINITE_ACTIVATION.md)。建议依次阅读 `Journal_Bounds` 的两槽载荷条件、`finite_activation_step` 的上限守卫、`finite_activation_history_valid`、`exhausted_run_keeps_epoch_and_stop`、`exhausted_floors_equal_limit` 及最后轮次可达见证。完整构建与十一组独立测试通过。这里证明编号载荷有界，不是整个存储空间有界；安全停发也不等于清场或急停。新的停发分支单独证明安全，没有直接套用旧事件系统的精化结论。

随后加入有限字节编码与字段适配，见 [EPOCH_BYTE_CODEC.md](EPOCH_BYTE_CODEC.md)。建议阅读 `epoch_encode`、`epoch_decode`、双向往返、`checked_successor_roundtrip`、`encoded_successor_matches_handoff`、`encoded_run_refines_finite` 与 `premature_truncation_changes_meaning`。完整构建和十二组独立测试通过；适配层精化目标是有限轮次协议，编码正确不等于报文认证或整个解析器正确。内部状态仍为数学状态，日志载荷可表示性不等于实际字节存储已经实现。

后续从上述定义导出了 SML 核心，见 [GENERATED_CODEC.md](GENERATED_CODEC.md)。建议先看 `Epoch_Codegen.thy` 的导出清单，再看自动生成的 `generated/EpochCodec.ML` 与独立文本入口；运行 `verify_generated_codec.ps1` 检查当前会话、导出来源、真实执行和错误副本。核心通过 405,588 条批量请求及两条交互检查；这补充了实际导出程序的执行证据，没有将编译器、运行时和手写入口纳入内核证明。

随后完成完整数据报层，见 [TUNNEL_FRAME.md](TUNNEL_FRAME.md)。建议依次读 `frame_config`、`frame_decode`、`frame_decode_exact`、`network_cannot_generate_ack`、`datagram_run_refines_finite`、`datagram_mutual_exclusion`，最后看尾随数据被错误截断的见证。25 个项目理论完整构建通过；导出报文核心通过 160,587 条批量请求、两条交互检查和真实错误副本控制，全套 17 个检查脚本通过。该层区分网络接收与本地权限，不把格式合法性当成来源认证；每次输入已经是一份完整数据报，并未形式化 socket 或字节流重组。

再后续的接收目标绑定见 [RECEIVER_BINDING.md](RECEIVER_BINDING.md)。建议依次阅读 `packet_destination`、`receiver_decode_exact`、`receiver_decode_unique_port`、`device_port_actions`、`controller_port_actions`、`receiver_run_refines_finite` 与忽略接收上下文的见证。27 个项目理论构建通过，导出接收检查核心通过 322,840 条请求、两条交互检查和错误副本控制，全套 20 个检查脚本通过。此处的接收位置是可信本地配置，不来自报文字段；Clear 报文的设备字段表示发送方标签，来源真实性仍不是目标检查能建立的事实。

## 新增：公平通行的正式证明

2026-10-02，完整会话再次构建成功，退出码 0。构建输出确认 `Tunnel_Liveness` 理论检查完成；会话约 6 秒，总计约 9 秒。该时长仅记录此次运行，不是基准测试。

### 假设的精确定义

`recurrent pi s` 表示：对于每个时间下界 n，都存在 m ≥ n，使执行在时刻 m 处于 s。

`transition_fair pi` 表示：对于每条具体状态转移 s → t，如果 s 反复出现，那么对于每个时间下界 n，都存在 m ≥ n，使 `pi m = s` 且 `pi (m+1) = t`。

这是真正的转移选择约束，不是“等待列车最终进入”的改写。它包括请求与空转转移，比弱动作公平性更强；本项目不声称这是最弱的充分条件，也不声称普通操作系统调度器自动满足它。

### 证明链

1. `reachable_permit_live`：在可达状态中，持有许可的列车不处于 Outside。
2. `release_holder`：持有许可的列车有合法路径完成进入或离开，并释放许可。
3. `waiting_has_entry_path`：每个可达等待状态，都存在一条使该列车进入的有限合法路径。这只是可达性，不预设调度器会选择它。
4. `recurrent_state_exists`：有限状态域上的无限执行包含反复出现的状态，复用标准库的无限鸽巢原理。
5. `recurrent_reachable`：在强转移公平下，从反复出现状态沿有限合法路径可达的状态也反复出现。
6. `fair_eventual_entry`：若执行合法、起点可达且满足强转移公平，那么对于每次等待，都存在更晚的进入时刻。
7. `fair_safe_service`：上述最终进入性质与全程安全性同时成立。
8. `endless_wait_is_not_fair`：先前持续停留于等待状态的反例不满足这个公平条件。

### 结论边界与辅助检查

没有导出等待秒数或步数上限；没有把公平路径筛选加入现有 CTLK 检查器。这里的新活性定理直接在无限执行上证明，原来无公平限制的 `AF` 反例保持不变。

独立 Python 检查构造了一条从初始状态出发并返回初始状态的 108 步闭合路径，覆盖正常模型的 12 个可达状态与全部 32 条不同状态转移。周期性重复此路径可满足强转移公平，说明该条件在这个独立枚举模型中可实现。108 是该见证的周期长度，不是通用等待上限。

这条周期见证目前只经过 Python 检查，尚未在 Isabelle 中证明它与抽象模型的对应及公平性。因此应区分：Isabelle 已验证的是带清楚假设的通行定理；公平执行存在性的这份具体见证仍是独立辅助证据。
