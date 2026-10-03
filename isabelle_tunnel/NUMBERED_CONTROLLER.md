# 带轮次编号的完成确认：验证结果与边界

## 检查结果

2026-10-02 18:30:51（Australia/Brisbane），Isabelle2025-2 完整构建 `Tunnel_Knowledge` 会话成功，退出码 0。输出包含 `Numbered_Controller` 理论检查完成；本次总计约 19 秒，不是性能基准。

新增理论为 `Numbered_Controller.thy`，导入已经验证的 `Delayed_Controller.thy`。没有用 `sorry`、`oops` 或新增公理替代证明。三个独立 Python 检查程序也通过；它们不是 Isabelle 认证导出的程序。

本次处理的是旧确认、重复确认与新编号层的形式化精化；随后进一步完成了原始报文响应条件到最终服务定理的证明。

## 为什么旧规则不够

原控制器只匹配列车和阶段。A 完成第一轮通行后，再次处于 Entering A 时，重放第一轮的进入确认也会被接受。错误不是两个请求计数相同，而是确认缺少所属轮次。

新状态增加自然数 `generation`。每次从 Ready 发起新的进入动作，编号增加一。该轮进入和离开共用编号，但使用不同报文类型：

| 报文 | 接受条件 |
|---|---|
| `Enqueue i` | 记录一次外部请求 |
| `Schedule` | 执行一次调度检查 |
| `EnterAck i k` | k 等于当前编号，并且阶段是 Entering i |
| `LeaveAck i k` | k 等于当前编号，并且阶段是 Leaving i |

不匹配的完成报文不改变状态。初始编号为 0，第一次授权后编号为 1。

## Isabelle 已验证什么

| 定理 | 精确作用 |
|---|---|
| `numbered_step_refines`、`numbered_trace_refines` | 去掉编号字段后，新模型的每步及整条执行对应延迟模型的一条执行 |
| `numbered_valid`、`numbered_safety` | 保持原不变量，两车不会同时持有区域保留标记 |
| `numbered_accounting` | 对于每个时刻及列车，received = pending + served |
| `generation_step`、`generation_monotone` | 编号每步保持或加一，沿执行不下降 |
| `admission_changes_generation` | 从 Ready 发起新一轮进入时，编号确实增加 |
| `mismatched_generation_ignored` | 与当前编号不符的进入和离开确认均被忽略 |
| `old_generation_stays_rejected` | 某编号小于当前编号后，在后续每个时刻继续被拒绝 |
| `entry_ack_idempotent`、`exit_ack_idempotent` | 同一完成报文连续处理两次，与处理一次的状态相同 |
| `release_requires_matching_packet` | Leaving 阶段缺少当前对象、当前编号的离开确认时，不释放该阶段与区域标记 |

精化证明中的 `silent_input` 只是把被拒绝报文对应到旧模型的一步状态不变转移。它不是向硬件发送的消息，也没有把拒绝报文改成可能推进调度的 Poll。

这些结果继承的是延迟控制器的安全与计数性质。没有据此证明延迟控制器与最早的八槽调度器等价；八槽上界仍不适用于本模型。

## 下一步已完成：用原始报文表达响应契约

`packet_responsive` 要求：

1. 对于每个时间下界，之后仍会出现 `Schedule`。
2. 对于每个等待进入或离开确认的时刻，之后会出现与该时刻的列车、动作类型和轮次编号相符的完成报文。

这允许报文延迟、插入陈旧或错误报文，没有预设服务结论，也没有限制到达耗时。

证明链是：

1. `waiting_packet_persistence`：没有匹配完成报文时，等待阶段与轮次编号保持。
2. `packet_response_trigger`：利用这种保持性，证明响应契约最终提供旧模型所需的推进事件。若此前已完成，则推进事件已经出现；否则等待阶段和编号仍与契约中的报文相符。
3. `packet_responsive_is_sufficient`：原始报文响应契约蕴含先前已证明足够的响应条件。
4. `packet_every_ticket_served`：设 target 是已被 received 覆盖的累计请求序号。在上述契约下，之后 served 会覆盖 target。

这里的“服务”仍指完成进入，不是整个旅程结束。离开确认负责释放区域标记，让后续请求继续推进。请求按每车累计计数建模，不包含载荷队列或请求消息去重。

## 仍不能声称解决的问题

- **伪造或错误完成信号。** `current_number_can_advance` 明确证明：若当前是 Entering i，填对当前编号的 EnterAck 会增加 served；该层不验证发件者或传感器。正确编号不是物理完成的证据。
- **重启与编号回绕。** 编号是无上限自然数，当前模型没有重启、持久化或有限位宽。重启后复用编号可能使旧包再次匹配，不能把当前防重放结论直接用于跨重启实现。
- **未来编号报文。** 不匹配当前编号时被忽略，但不保证一个报文在编号后来匹配时仍被拒绝。防伪造需要另加来源和会话约束。
- **请求重复投递。** 完成确认有编号，Enqueue 没有请求 ID；重复 Enqueue 会被记录为多次请求。
- **真实位置与设备故障。** zone 仍是控制器的保留标记，不是独立的物理位置。现实不碰撞还依赖设备服从命令及完成信号真实等契约。
- **实时性和实现。** 没有秒数上界、超时恢复、并发实现、认证协议实现或硬件部署。

后续建议先区分“可信来源”与“物理完成事实”：形式化设备状态及允许产生确认的条件，再证明控制器区域标记覆盖真实占用。仅加一个名为 authenticated 的布尔值，并不能验证真实认证协议或传感器。

这项后续工作现已在独立的 `Physical_Controller.thy` 与 `Physical_Recovery.thy` 中推进并通过 Isabelle 检查：在明确的设备动作、真实读取及可信来源规则下证明占用安全，加入保留状态重启、旧会话隔离和合作恢复服务。见 [设备与重启恢复报告](PHYSICAL_RECOVERY.md)。本文件的编号层本身保持原定义，仍不承担来源认证；新增层也没有验证实际密码算法、传感器或持久化实现。

## 独立检查

`check_numbered.py` 检查了：

- 两次同车通行中，旧模型接受陈旧确认，而新编号层拒绝它。
- 陈旧编号、未来编号、错误对象、错误动作类型及连续重复完成确认。
- 正确当前编号仍会被接受这一安全边界，避免误报为已解决认证。
- 固定随机种子的 20,000 次报文转移，逐步检查精化、编号变化、计数守恒与互斥。
- 上述测试接收 4,998 次请求；在随后持续提供匹配完成报文并插入陈旧报文的测试中，A 完成 2,539 次、B 完成 2,459 次，队列清空。

这些是有限测试，不代替 Isabelle 的通用定理。原有 `check_model.py` 和 `check_delayed.py` 也重新通过。

## 复现与阅读

完整 Isabelle 构建方式见 [README](README.md)。独立检查：

```powershell
python .\isabelle_tunnel\check_model.py
python .\isabelle_tunnel\check_delayed.py
python .\isabelle_tunnel\check_numbered.py
```

建议按 `decode` → `numbered_react` → `numbered_trace_refines` → `old_generation_stays_rejected` → `packet_responsive` → `packet_every_ticket_served` → `current_number_can_advance` 阅读。
