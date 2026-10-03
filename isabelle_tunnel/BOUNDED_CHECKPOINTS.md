# 有限编号与检查点：复核及下一步验证结果

## 正式检查结果

2026-10-02 19:18:44（Australia/Brisbane），Isabelle2025-2 完整构建 `Tunnel_Knowledge` 会话成功，退出码 0。构建包含原有理论和新增三份理论，总计约 24 秒；该记录不是性能基准。

本轮先重新构建并复核上一轮项目，同时做了独立的定理／报告范围审查；随后完成：

1. `Bounded_Identifiers.thy`：有限编号、耗尽锁定、安全保持、在途任务清空和编号重用反例。
2. `Checkpoint_Journal.thy`：带提交状态的双槽检查点与抽象崩溃一致性。
3. `Checkpoint_Integration.thy`：检查点完整性不能独自保证设备恢复安全的形式反例，以及一个正确提交的对照例。

新增证明没有使用 `sorry`、`oops` 或新增公理代替证明。独立 Python 测试是补充证据，不是认证代码生成结果。

## 一、有限编号层

### 精确策略

G 是轮次编号上限，E 是会话编号上限。初始两个编号均为 0。

- 未锁定且尚有编号空间时，沿用此前已经验证的设备控制规则。
- 处于 Ready 且轮次编号已到 G 时，下一次调度检查进入锁定，不发新许可。即使当前没有排队请求，也会锁定。
- 会话编号已到 E 时，Restart 输入进入锁定，不通过回绕产生新会话。
- 锁定时保留控制状态、许可、计数和编号。
- 锁定后停止处理请求、轮询、确认和重启；此前已经授权的设备进入／离开动作仍按旧阶段规则执行。

这叫控制处理锁定，不是物理急停。处于 Entering 的设备在锁定后仍可能进入；处于 Occupied 的设备则可能因为无法获得离开命令而一直保留占用。这里证明的是占用互斥，不是锁定后自动清场。

Restart 仍是抽象输入。拒绝一次逻辑重启并保留状态，不能直接解释成真实断电后内存仍存在。

### 已验证的性质

| 定理 | 结论 |
|---|---|
| `bounded_step_valid`、`bounded_history_valid` | 有限编号策略保持原设备不变量和编号范围 |
| `bounded_identifiers` | 对于每个可达时刻，generation ≤ G，era ≤ E |
| `bounded_generation_monotone`、`bounded_era_monotone` | 两个编号沿执行不下降，不因耗尽而回绕 |
| `bounded_physical_safety` | 原设备占用互斥性质保留 |
| `bounded_accounting` | 已接受请求的 received = pending + served 关系保留 |
| `lock_persists`、`locked_run_keeps_machine` | 锁定持续存在，后续每个有限事件序列都不改变控制器状态 |
| `locking_preserves_snapshot` | 触发锁定本身不会清空许可或排队请求 |
| `finite_width_representation`、`wire_identifier_roundtrip` | 上限设为 2 的幂减一时，编号在对应数值范围内，按该模数计算不会改变编号值 |

最后一项是自然数范围和取模恒等式，不是具体机器字算术、二进制解析器、网络编码或 C 程序的精化证明。只有编号有上限；请求计数和来源记录仍使用无上限的数学对象，所以整个模型不是有限内存实现。

锁定前仍能接收新的请求，但不再保证它们有足够的编号得到服务；锁定后的请求输入被忽略，不计为已接受请求。实际接口还需要向调用方明确返回拒绝或不可用状态。

### 在途任务可以先结束

`active_visit_can_clear` 证明：设系统满足不变量、尚未锁定且正在执行一轮通行，即使编号已经达到上限，仍有一条不插入重启的合作执行可以完成当前通行，回到 Ready，并使两车都在区域外。此过程不消耗新编号。

`clearance_events` 给出的序列为：

| 起始阶段 | 动作序列长度 |
|---|---|
| Entering | 7 个模型事件 |
| Occupied | 4 个模型事件 |
| Leaving | 3 个模型事件 |

`clearance_length_bound` 证明长度至多为 7。事件包括设备完成移动、读取和送达确认；这不是七个时钟周期，也没有现实秒数上限。若中途触发会话耗尽锁定，不能继续套用这条未锁定条件下的结论。

### 不能继续沿用无限服务结论

`exhaustion_keeps_unserved_request` 给出编号上限为 0 的明确例子：A 的一次请求已记录，但调度触发锁定后 pending 为 1、served 为 0。结合锁定后控制状态保持定理，不能声称这些请求以后仍必定得到服务。

因此本轮区分了安全性和可用性：宁可保留请求及许可并锁定，也不通过重复使用旧编号恢复推进。

### 编号重用的正式反例

`authentic_replay_after_reuse_collides` 验证了一条错误方案：A 完成一轮通行后，把后续新编号重新设为 1，同时保留旧的真实确认报文。第二轮 A 仍在区域内时，重放第一轮的真实离开确认，控制器会错误释放许可，随后 B 可以进入，形成双车占用。

这次没有伪造传感器来源；问题是旧编号被重用。来源可信与编号新鲜是两个不同条件。

## 二、双槽检查点

### 状态与动作

每个槽为 Empty、Partial(payload) 或 Complete(payload)。另有活动槽选择器和待提交事务标志。初始种子检查点已经完整提交。

1. Prepare 把非活动槽写成 Partial，并开始一个待提交事务。
2. Flush 在待提交事务内把该槽变成 Complete。
3. Commit 只在该事务存在且非活动槽完整时切换选择器，并清除待提交标志。
4. Crash 丢弃 Partial 内容、清除待提交标志，但保留 Complete 内容和活动选择器。

模型中的提交历史是证明辅助状态。恢复函数只读取被选择的槽，不通过一份“已知正确答案”来检查磁盘内容。

### 已验证的性质

- `selected_record_is_complete`：恢复选择的记录是 Complete，不是部分写入记录。
- `restore_is_latest_commit`：恢复值对应最近一次成功的选择器提交。
- `partial_write_crash_keeps_checkpoint`：部分写入期间崩溃，仍恢复前一份检查点。
- `flushed_write_crash_before_commit_keeps_checkpoint`：数据已完整写入但尚未提交时崩溃，仍恢复前一份检查点。
- `committed_write_survives_crash`：成功提交后崩溃，恢复新检查点。
- `repeated_commit_is_idempotent`：重复 Commit 不会切回旧槽。
- `crash_aborted_commit_is_ignored`、`crash_aborted_flush_is_ignored`：崩溃已取消的事务不能靠后续 Commit 或 Flush 启用残留数据，需要重新 Prepare。

### 存储前提没有消失

此证明假定 Flush 使完整记录持久化、选择器提交具有原子性且持久化、崩溃不损坏 Complete 记录。没有验证 Windows、文件系统、磁盘控制器、断电保护或存储 API 确实满足这些条件。

模型还允许调用方明确 Prepare 一个旧载荷；它阻止的是意外的选择器重复切换，不是识别每个载荷在应用层是否足够新。恶意回滚、篡改、密钥管理和实际校验算法仍在范围之外。

## 三、集成反例：完整不等于足够新

`Checkpoint_Integration.thy` 将检查点载荷设为控制器状态，保持独立的设备占用不变。

反例过程：初始检查点仍表示区域空闲；A 已获准进入且尚未离开。程序准备把当前控制器状态存入检查点，完成 Flush，但在 Commit 之前崩溃。双槽协议正确地恢复了前一次完整提交，即旧的空闲状态。

`intact_journal_can_lose_physical_coverage` 与 `interrupted_restoration_breaks_physical_invariant` 证明：检查点自身有效、恢复行为也符合双槽协议，但恢复后的控制器没有覆盖仍在区域内的 A。旧检查点不是坏数据，它只是提交得太早。

对照例先完成 Commit 再崩溃，能够恢复该例的当前控制状态并保留占用覆盖。这个正例不等于已经证明了一套通用控制器持久化协议。

因此下一项关键工作是将持久化和设备动作真正关联起来：发出进入许可之前先提交相应的许可、轮次和会话信息，并证明崩溃后恢复的保留状态足以覆盖尚未完成的设备动作。本轮给出了该义务的形式依据，没有将它假装成已完成的联动证明。

## 独立测试与复核

原有四组测试继续通过。新增测试：

| 程序 | 覆盖 |
|---|---|
| `check_bounded.py` | 上限 0–3 的 16 个组合；16 万次固定种子事件转移；锁定保持、在途清场和旧编号真实报文重放反例 |
| `check_journal.py` | 三种载荷下长度为 6 的 46,656 条事件序列；10 万次固定种子转移，1,962 次成功提交与独立事务记录一致；崩溃边界、重复提交和检查点集成反例 |

它们是有限测试，不是形式定理的替代品。另有独立阅读审查核对前一轮报告与定理的对应，以及本轮锁定、位宽和检查点规则的结论边界。

## 文件与复现

三份新增理论已接入 `ROOT`。完整 Isabelle 构建方式见 [README](README.md)。新增补充检查：

```powershell
python .\isabelle_tunnel\check_bounded.py
python .\isabelle_tunnel\check_journal.py
```

建议阅读顺序：`limit_guard` → `bounded_step_valid` → `active_visit_can_clear` → `authentic_replay_after_reuse_collides` → `journal_step` → `restore_is_latest_commit` → `intact_journal_can_lose_physical_coverage`。

## 后续进展

本报告之后新增的 [持久许可联动验证](DURABLE_ADMISSION.md) 已完成独立准入核心的正式证明：先提交许可再发命令，且许可交接需要设备退出并清空在途命令。该模型保留跨崩溃的设备动作，没有宣称完整编号控制器、实际磁盘或清场通信协议已经验证。
