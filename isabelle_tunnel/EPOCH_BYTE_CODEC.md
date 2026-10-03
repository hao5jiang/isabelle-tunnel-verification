# 轮次字段的有限字节编码：Isabelle 验证报告

日期：2026-10-03。

## 结果

已完成固定字节数的小端轮次编码、严格解码、受保护的递增，以及它们与有限轮次协议的对应证明。

新增 `Epoch_Byte_Codec.thy`、`Encoded_Activation.thy` 已接入 `ROOT`，包含 48 条引理／定理声明。2026-10-03 08:55:08（Australia/Brisbane），Isabelle2025-2 完整会话构建成功，退出码 0，总计约 35 秒。项目的 21 个理论文件一起通过；十二组独立 Python 测试全部通过。

本轮验证的是轮次字段算法及其协议适配层，不是完整网络报文解析器、原生机器字运算、实际磁盘布局或固件。

## 编码格式和接受条件

设 n 是字节数，L 是执行期间不变的轮次上限。容量为 `256^n`，配置要求 `L < 256^n`。每个字节由范围在 0–255 的自然数表示。

例如两字节小端编码：`513 ↔ [1, 2]`，因为 `513 = 1 + 256 × 2`。

受检查的编码器只有在配置有效且 `k ≤ L` 时返回恰好 n 个字节。解码器只有在以下条件同时成立时才接受：

1. 配置有效。
2. 输入长度恰好为 n。
3. 每项都小于 256。
4. 小端数值不超过 L。

因此不通过裁去多余字节、把非字节项掩码、或对大编号求余来“修复”输入。失败返回 `None`；适配层不执行对应协议动作。

`epoch_bytes` 是底层定长生成函数，本身不保证大输入可表示。对外使用的 `epoch_encode` 加入范围条件。只调用底层函数会丢失这个保护。

数学模型也包含 n=0、L=0 的退化情形：空列表表示 0，没有后继轮次。这不是推荐的部署格式；应用可以额外要求 n≥1。

## 已证明的编码性质

| 定理 | 内容 |
|---|---|
| `epoch_bytes_length`、`epoch_bytes_digits` | 输出长度正确，每个输出项属于字节范围 |
| `epoch_value_bound` | 合法 n 字节列表的数值小于容量 |
| `epoch_value_bytes`、`epoch_bytes_value` | 容量内数值和合法定长字节列表双向往返不变 |
| `epoch_checked_roundtrip` | 编码成功后，解码恢复原编号 |
| `epoch_decode_reencode`、`epoch_decode_injective` | 接受的列表是规范表示；同一配置下，两份接受的表示若解码相同，它们必然相同 |
| `epoch_decode_rejects_length`、`nonbyte`、`range`、`configuration` | 长度错误、非字节项、超上限或配置无效均拒绝 |
| `checked_successor_roundtrip` | 成功的后继结果解码为 k+1，严格增加且不超过 L |
| `checked_successor_at_cap` | 当前编号已经达到 L 时，没有可接受的后继结果 |
| `guarded_increment_mod_identity` | 守卫允许递增时，新数值仍在容量内，求余不会改变它 |
| `unchecked_increment_wraps` | 容量边界上，无保护的模递增回到 0 |

拒绝性质一行的四个短名称均带 `epoch_decode_rejects_` 前缀。

`encoded_successor_matches_handoff` 进一步把成功后继与真实模型动作连接：编码的 k+1 正是 `BeginHandoff` 放进非活动日志槽的候选轮次。`encoded_successor_matches_exhaustion` 则证明到达上限时，后继返回失败，协议对应只设置停发标志。

这里的递增函数先以解码结果和上限判断是否存在后继。证明依赖数学整数计算；没有据此宣称底层程序的内存操作、溢出行为或实际求值顺序已经检查。

## 字节输入怎样接入协议

| 适配事件 | 原有限协议动作 | 含义 |
|---|---|---|
| `EntryField` | `DeliverEntry` | 投递进入命令 |
| `FenceField` | `DeliverFence` | 投递轮次隔离请求 |
| `AckField` | `SendClearAck` | 请求设备依照原门槛与实际占用规则生成确认 |
| `ReceiveField` | `ReceiveClearAck` | 接收已发出的确认 |

`AckField` 不是把外部字节直接当成真实清场证据。设备仍须通过原协议的在线、门槛、请求来源和实际占用检查。`ReceiveField` 才对应确认接收动作。类型和设备身份仍使用已有的类型化字段，尚未序列化为完整报文。

主要对应定理：

- `encoded_field_roundtrip_exact`：合法轮次经过字节编码后，适配结果与原有限协议的同一步相等。
- `encoded_field_rejected_stutters`：拒绝的轮次字段不改变协议状态。
- `encoded_step_refines_finite`：每个适配步骤是原有限协议的一步或停留。
- `encoded_run_refines_finite`：将拒绝项从解码事件序列中去掉后，两条有限执行的最终状态严格相等。
- `encoded_activation_history_valid`、`encoded_activation_mutual_exclusion`：包含畸形输入的事件序列仍保持范围与互斥安全。
- `encoded_exhaustion_survives`：达到上限且停发后，经该适配层执行仍保持轮次和停发状态。

这个精化目标是 `Finite_Activation`，没有补上上一轮明确保留的“整个有限包装器到更早消息模型”的精化义务。

`TrustedLocal` 是内部已构造事件入口，不经字节解码，继续使用有限协议的规则。因此配置无效只使编码／解码拒绝，不能表述为“整个控制器停机”或“本地动作也停止”。它不是提供给不可信原始报文的备用入口。

## 两槽中的编号是否也能表示

`complete_storage_payloads_representable` 证明：有效状态下，控制器两槽和提交历史中的轮次，以及每个设备两槽和提交历史中的门槛，都存在能够准确往返的字节表示。部分记录也在范围内。

`controller_and_device_values_serialize` 与 `issued_epoch_serializes_exactly` 还覆盖当前控制器轮次、磁盘门槛、生效门槛和已发命令编号。

这些结论是载荷可表示性，不是已经把日志存储改为字节，也没有验证日志格式、磁盘写入或校验码。

## 正式验证的错误示例

上限为 1、字段为一个字节时，列表 `[257]` 不是合法字节输入；直接编码数值 257 也失败。

错误路径先执行截断：

`[257] → 数值 257 → 只保留一个字节 [1] → 被解码为轮次 1`

`premature_truncation_changes_meaning` 给出协议内见证：在 A 的最后轮次命令已发出、系统已停发但尚无实际占用的可达状态中，严格入口拒绝 `[257]`，错误截断入口却把它解释成有效的轮次 1 命令，导致 A 进入。

这证明的是输入含义被改变、拒绝策略被绕过，不是双占用碰撞。原协议对同一轮次合法旧命令的重放本来就允许；本轮没有把范围校验说成防重放或身份认证。

## 独立测试

新增 `check_epoch_codec.py`，使用标准库的整数／字节转换作独立对照：

- 一字节范围：65,536 次解码、65,536 次编码，32,896 个接受的往返。
- 二字节最大上限：完整覆盖 65,536 个值，检查双射。
- 0、1、2、4、8 字节共 1,963 个边界／畸形用例。
- 84 条固定种子的协议轨迹，22,440 次转移；其中 11,446 个输入被拒绝。逐步和整段轨迹都与解码后的有限协议对照。
- 检查上限后继拒绝、末轮停发后的旧命令执行、截断回绕、非字节掩码，以及增加高位零字节导致的长度混淆。

Python 是独立模型，不是 Isabelle 认证导出的程序。它还拒绝负数、非整数及布尔值；这些对象不属于 Isabelle 的自然数列表输入域。其可信本地事件测试选用非轮次字段事件，不表示已经穷举 `TrustedLocal` 的完整类型空间。

## 范围与下一步

本轮没有验证：完整报文布局与帧边界、消息类型／身份字段解析、网络认证、物理传感器、实际字节存储、原生固定宽整数、编译器、内存分配，以及巨大输入的资源消耗。配置 n/L 仍须在同一执行期间保持一致。

独立只读审查已检查编码规范性、守卫边界、适配器与已有证明的连接，并特别核对了确认生成和确认接收的区别。形式检查没有用 `sorry` 或新增公理代替证明。

后续已从 Isabelle 导出可运行的编码／解码与后继函数，并对真实导出程序完成 405,588 条请求及两条交互检查，见 [GENERATED_CODEC.md](GENERATED_CODEC.md)。现已从独立模型测试推进到对正式定义导出程序的执行测试；编译器与运行时仍属于可信边界。

## 文件与复现

完整 Isabelle 构建方法见 [README](README.md)。新增独立测试：

```powershell
python .\isabelle_tunnel\check_epoch_codec.py
```

核心文件：`Epoch_Byte_Codec.thy`、`Encoded_Activation.thy`、`check_epoch_codec.py`。
