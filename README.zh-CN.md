# Turing Universality in Hypergraph Turán Theory

本项目把论文 **Theorems 1.1、1.2、1.3** 整理为一个独立的 Palomar 提交项目。
形式化作者及维护者为 **Xizhi Liu**；数学原论文作者为 **Heng Li、Xizhi Liu**。
公开仓库：[xliu2022/turan-universality-lean](https://github.com/xliu2022/turan-universality-lean)。
原论文题目为 *Turing universality, computability, and incompleteness in
hypergraph Turán theory*，采用所提供的 2026 年 11 月 8 日 V4 稿件。

## 包含什么

| 文件或目录 | 用途 |
| --- | --- |
| `Challenge.lean` | 三个完整数学陈述及所需定义；只依赖 Mathlib |
| `Solution.lean` | 三个对应的证明入口 |
| `comparator.json` | 唯一提交配置，同时比较三个主定理 |
| `TuranUniversality/` | 三个证明共同需要的全部 419 个项目源码模块 |
| `TuranUniversality.lean` | 汇总三个证明根模块 |
| `lean-toolchain`、`lakefile.toml`、`lake-manifest.json` | 固定 Lean、Mathlib 及传递依赖版本 |
| `formalization.yaml` | 标题、摘要、作者、来源、AI 辅助及审阅状态 |
| `verification/combined/` | 此次合并后的实际构建、比较、公理与内核验证记录 |
| `verification/merge/` | 源码依赖闭包、合并来源及数学忠实性审查 |
| `proof-exports/` | 此次实际核验的两份完整证明导出，使用 gzip 压缩保存 |
| `scripts/`、`.github/workflows/` | 检查脚本和 GitHub 验证工作流 |
| `source/` | 所提供 V4 原论文的 TeX 源文件 |
| `LICENSE`、`NOTICE` | 代码许可证及复用来源说明 |

这是完整的项目源码包。Lean 工具链、Mathlib 和构建缓存按锁定版本获取，
不作为压缩包内的预编译依赖分发。
随包提供的导出证书可供直接内核重放；它们不是编译所需依赖。
该目录已加入 `.gitignore`，上传源码仓库时可以不提交这些生成数据。

## 如何编译

安装 Elan 后，在解压所得项目目录执行：

```sh
lake exe cache get
lake build
python3 scripts/check-lean-sources.py
```

正常的沙箱比较与内核预检命令为：

```sh
bash scripts/verify-comparator.sh
```

Lean 固定为 `v4.35.0-rc2`，Mathlib 固定为
`065356127b1dc0016f66b7283ce0ce2c4055aa55`。

2026 年 11 月 25 日，Palomar 对提交 `971e68d2122c3901a73a6187ce96ffc97d0f0729`
完成了正式机械验证。`comparator.json` 选定的三个定理均通过陈述比较和公理检查，
Lean、NanoDa 和 con-ron 均接受了导出的证明。[官方验证记录](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45563382429)

此前准备发布包时，本地 `bubblewrap` 因无法打开 `NETLINK_ROUTE` 套接字而启动失败。
同次准备中的本地构建、公理检查以及 Lean 和 NanoDa 的独立重放成功。
详情见[验证历史](docs/VERIFICATION.md)和[本地检查记录](verification/combined/RESULTS.json)。

## 本次整理的准确范围

1. **1.1**：单个禁用三一致超图、固定有理阈值、停机与密度二分，以及真正的原始递归编译器。
2. **1.2**：对每个一致度 `r ≥ 3` 给出有限禁图族及精确密度缩放；族编译器关于 `r` 与输入字串联合原始递归，模板编译器关于 `r` 原始递归。固定模板与输入无关，其均匀权重全局最优，且所有 blowup 都避开对应禁图族。
3. **1.3**：对一个固定阈值以上的所有一致度，给出关于一致度与字串联合原始递归的结构编译器。非停机时有唯一极值轮廓及原顶点集上的编辑稳定性；停机时有两个非空、不交的紧相，每相均与整个内层极值空间同胚，整个外层空间与 `Bool` 和内层空间的乘积同胚。

三个公开定理保留各自的存在量词，没有因合并而增加“见证必须相同”的新断言。
形式化采用已验证的机器、编码和常数实现；并未声称逐步等同论文机器、
给出所有常数的具体数值，或已经提取可执行编译器。详细对应关系见
`verification/merge/statement-fidelity.md`。

**Theorem 1.4、ZFC 内部化、后续独立项目和超越密度部分不在本次提交范围。**
被证明依赖的辅助结果保留在源码中；本项目不宣称整篇论文已经完成形式化。

`Challenge.lean` 中三处 `sorry` 是陈述比较所需的预期占位。
完成的 `Solution` 及其证明依赖不使用这些占位；没有未完成证明。

## 上传时使用什么

使用公开仓库 **`xliu2022/turan-universality-lean`** 和待审查提交的完整 40 位 SHA。
Lean 项目位于仓库根目录，提交表单中的可选项目路径和元数据路径可以留空。
Palomar 选择 **`comparator.json`**，即可同时指定三个定理；无需分别提交三份。
提交时需要公开仓库及完整 40 位 commit SHA。提供的官方预检工作流需手动运行。

可在 [GitHub Actions](https://github.com/xliu2022/turan-universality-lean/actions/workflows/palomar-full.yml)
运行完整预检，并选择通过预检的准确提交。预检不会自动提交或注册；
后续由维护者在 [Palomar 提交网站](https://submit.palomar-registry.org/)办理。
发布包和验证记录保留原始整理时的发布状态。
