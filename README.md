# Isabelle Tunnel Verification

两列车共享隧道的 Isabelle/HOL 形式验证项目。从许可与知识性质出发，逐步加入延迟确认、轮次隔离、崩溃恢复、持久化、有限编号、报文编码和接收目标检查。

这是个人研究项目，不是可部署的铁路控制系统，也不是参考书第 8 章的完整形式化。

## 已验证范围

- 协议互斥安全、明确公平性条件下的通行，以及具体调度器的离散等待界限。
- 持久化与内存启用分离、设备恢复、有限轮次耗尽后的安全保持。
- 严格报文字段与完整数据报编解码、接收目标绑定。
- 错误设计的形式反例，以及直接导出的 SML 程序执行检查。

2026-10-03 的本地验证记录包含 27 个项目理论、20 个检查脚本。最近的接收目标检查核心通过 322,840 条实际请求；记录和假设见 [接收目标绑定报告](isabelle_tunnel/RECEIVER_BINDING.md)。

## 阅读入口

- [项目演进与来源](isabelle_tunnel/README.md)
- [Isabelle 导读](isabelle_tunnel/ISABELLE_GUIDE.md)
- [有限轮次集成](isabelle_tunnel/FINITE_ACTIVATION.md)
- [完整报文格式](isabelle_tunnel/TUNNEL_FRAME.md)
- [接收目标绑定](isabelle_tunnel/RECEIVER_BINDING.md)

## 复现

使用 Isabelle2025-2，在仓库根目录执行：

```sh
isabelle build -D isabelle_tunnel
```

Python 模型检查需要 Python 3.10 或更高版本，使用标准库：

```sh
python isabelle_tunnel/check_model.py
```

实际导出程序检查另需 Poly/ML 5.9.2。可明确指定运行器：

```sh
python isabelle_tunnel/check_generated_receiver.py --polyml /path/to/poly
```

或者设置 `POLYML` 环境变量为运行器完整路径，再运行检查脚本。没有该变量时，测试器从 PATH 查找 `poly`。

Windows 一键复查会重建会话、比对当前导出、运行实际程序及错误副本控制：

```powershell
& .\isabelle_tunnel\verify_generated_receiver.ps1 -IsabelleRoot 'C:\Tools\Isabelle2025-2' -Python python
```

其中安装路径是示例，请改成自己的安装目录。脚本默认使用该 Isabelle 安装内的 Windows Poly/ML，可通过 `-PolyML` 覆盖。`-Smoke` 使用较小的实际执行测试集。

## 发布副本与历史记录

理论文件与生成的 SML 核心保持原样。发布整理只替换了个人路径、改进本地工具发现，并增加仓库说明；原工作目录保留不动。

`CODEGEN_MANIFEST.json`、`FRAME_MANIFEST.json`、`RECEIVER_MANIFEST.json` 是各轮本地验证的历史快照，不能据其旧哈希声称发布副本中的说明和运行脚本从未改变。发布文件哈希另见 `PUBLICATION_MANIFEST.json`。哈希记录不是签名，也不是认证机制。

本仓库不包含参考书 PDF、账号凭据、浏览记录、音频项目或构建缓存。书目来源保留在项目说明中。尚未选择对外分发许可证。

## 边界

结论依赖各模型明确写出的可信来源、占用观察、持久化及原子动作假设。目标字段检查不是来源认证；可信接收参数与真实通信接口的绑定、密码实现、实际存储、固件、传感器和编译器正确性均未完成形式验证。
