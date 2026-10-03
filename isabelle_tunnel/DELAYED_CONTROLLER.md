# 外部请求与延迟完成确认：Isabelle 验证结果

## 正式检查

2026-10-02，使用 Isabelle2025-2 构建完整 `Tunnel_Knowledge` 会话，结果成功、退出码 0。输出确认 `Delayed_Controller` 理论完成，会话约 18 秒，总计约 23 秒；不是性能基准。

新增证明没有使用 `sorry`、`oops` 或新增公理。正式结果来自 Isabelle，不来自 Python 测试。

## 为什么另建模型

旧模型假定持续请求、动作在一个调度槽内完成。新模型区分请求、发出动作以及收到完成确认，输入来自外部事件流。因此另定义状态与执行函数，并保留旧文件及其结论。

没有证明新旧控制器之间的精化关系；八槽上界仅属于旧模型。新模型中的请求计数没有上限，不是先前 12 状态图的简单扩充。

## 状态与输入

| 阶段 | 含义 | 推进条件 |
|---|---|---|
| Ready | 没有活动列车 | Poll 检查请求并选出服务对象 |
| Entering i | i 已获独占许可，进入动作尚未确认完成 | EntryDone i |
| Occupied i | 已确认 i 进入 | Poll 发起离开动作 |
| Leaving i | 等待 i 的离开完成确认 | ExitDone i |

输入还有 `Request i`：在每个阶段都增加该列车的请求计数，不覆盖已有请求。匹配不到当前阶段或对象的完成输入被忽略。

Ready 阶段优先选择 `priority` 指定的列车；若它没有请求，则检查另一列车。授权后把下一次优先权交给另一车。同一时刻最多有一个活动对象。

每列车有三个自然数计数：`received` 为已接收数，`pending` 为未完成进入的数量，`served` 为已确认完成进入的数量。这里的“服务完成”是进入完成，不是整段旅程结束；离开确认负责释放独占许可。

每次授权不会减少 pending。只有当前活动列车的进入完成确认，才会把一份 pending 转为 served。

## 安全与请求保留

| 定理 | 含义 |
|---|---|
| `react_valid`、`history_valid` | 每个输入处理保持不变量，执行中的每个状态有效 |
| `request_is_recorded` | 每个请求输入使 received 与 pending 分别加一 |
| `no_lost_requests` | 对于每个时刻和列车，received = pending + served |
| `service_requires_entry_confirmation` | served 增加只能来自匹配当前 Entering 阶段的进入确认 |
| `pending_persists` | 如果本步没有服务完成，pending 不减少 |
| `delayed_safety` | 两列车不会同时持有 zone 标记 |
| `exit_confirmation_required` | 在 Leaving 阶段，除匹配离开确认外的输入不解除该阶段与 zone 标记 |
| `entry_delay_keeps_reservation` | 等待进入完成确认时也继续保留 zone 标记 |

`zone` 是保守的独占区域标记：从进入命令发出就设为真，直到离开完成确认才设为假，覆盖进入途中、已进入和离开中的整个阶段。它不是独立测量的物理坐标。把模型互斥解释为现实不碰撞，需要设备服从命令、完成信号真实等额外前提。

请求在模型中按每车计数区分次数；没有请求载荷、网络消息 ID 或用户身份。累计请求序号被完成计数覆盖的结论，不等于验证了一套带载荷的 FIFO 消息系统。

## 最终服务依赖什么

`responsive ev` 明确要求：

1. 对于每个时间下界，之后仍有 Poll 输入。
2. 每次处于 Entering i，之后会有 EntryDone i 输入。
3. 每次处于 Leaving i，之后会有 ExitDone i 输入。

这没有预设请求最终服务，也没有给出完成耗时上限。定理利用状态持续性，保证在尚未完成动作时，相应完成输入会有效推进它。

- `next_service`：若 pending 为正且事件流满足 responsive，则之后 served 会增加。
- `every_ticket_served`：如果某个累计请求序号已被 received 覆盖，则之后 served 也会覆盖这个序号。
- `each_request_event_served`：请求输入发生后的累计请求计数最终得到服务覆盖。

证明先假设目标列车一直未得到下一次服务，推出其 pending 持续为正；再构造非递增的自然数进展度量，证明对应轮询或完成输入会严格降低度量，产生矛盾。随后对目标请求序号做归纳。该证明允许后续继续到达新的请求。

## 完成信号缺失时

`missing_completion_stalls` 正式构造了反例：A 请求、获授权之后，只持续收到 Poll 而没有进入完成确认。经过每个后续有限前缀，A 的 pending 仍为 1、served 为 0、zone 为真，B 的 zone 为假。

因此不能删去响应条件后仍声称最终通行。控制器不会为了推进队列而提前释放许可。这里没有证明具体超时恢复策略。

## 环境与实现边界

- 当前模型按列车和阶段匹配确认，尚无动作序号或会话 ID。某条旧信号若恰好与后续同车同阶段重合，可能被接受；本次不证明防重放。
- 完成信号的真实性与新鲜度是环境契约，不是 Isabelle 已验证的传感器性质。`responsive` 只表达最终到达，不单独编码物理真实性。
- 自然数计数不溢出；实际内存容量与整数溢出未建模。
- 没有时钟或动作完成时限，因此没有新的固定等待步数或秒数上界。
- 新模型没有被导出或部署为驱动、PLC 或并发程序。

## 独立测试

`check_delayed.py` 使用另一份实现做补充检查：

- 将 pending 限制在每车 0–2，并把累计计数归一化后的结构搜索，覆盖 66 个状态与 416 条输入转移。
- 连续接收 A 三次、B 两次请求，验证最终分别完成 3 次、2 次服务。
- 延迟 100 次轮询并插入错误对象的离开确认，验证许可不提前释放。
- 永久缺少进入确认的有限前缀测试，验证请求仍保留且服务不虚增。

结构搜索有界、计数经过归一化，不能替代自然数队列的通用定理。Python 不是 Isabelle 认证导出的程序。

## 复现与阅读

按 README 的命令构建整个会话。独立测试：

```powershell
python .\isabelle_tunnel\check_delayed.py
```

建议在 Isabelle/jEdit 中依次阅读 `react`、`valid`、`no_lost_requests`、`responsive`、`next_service`、`every_ticket_served` 和 `missing_completion_stalls`。

后续增强已在独立的 `Numbered_Controller.thy` 中完成：引入轮次编号，证明旧编号拒绝、连续重复确认幂等，以及到本延迟模型的精化和报文响应条件下的最终服务。见 [编号确认层报告](NUMBERED_CONTROLLER.md)。本文件描述的原始无编号模型保持不变，其旧消息风险也仍存在；新层没有解决来源认证、物理真实性、重启回绕或响应时限。
