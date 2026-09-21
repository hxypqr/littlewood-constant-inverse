# 验证说明

版本固定为 Lean 4.32.0、mathlib v4.32.0；完整提交号在 `lake-manifest.json`。验证使用 Lean 实际构建和声明依赖检查，数值证书也由 Lean 检查。

本次最终验证：**137 个正式模块、1,219 条定理（其中 1,216 条公开定理逐条核查公理依赖），整体构建及全部依赖检查通过。** 源码中没有证明占位、未经许可的公理或遗漏导入的正式模块。机器可读结果及逐文件 SHA-256 见 `validation_summary.json`。

```text
lake build
python verification/generate_audit.py --strict
lake env lean AuditAll.lean
lake env lean Audit.lean
lake env lean verification/MainTheoremsAudit.lean
lake env lean verification/AppendixBAudit.lean
```

Python 步骤只重新生成审计清单；交付中已包含 `AuditAll.lean`，因此普通构建与证明核验不需要 Python。

| 文件 | 核查内容 |
|---|---|
| `build.log` | 整体工程构建结果 |
| `all_axioms.log` | 所有公开定理的实际依赖 |
| `axioms.log` | 主要定理、一般群版本和附录结果的类型及依赖 |
| `main_theorems_axioms.log` | 两个主定理及两个主要推论 |
| `appendix_b_axioms.log` | 附录 B 的系数、谱界、尖锐性、相位和最终渐近 |
| `declarations.json` | 根模块导入闭包中的定理、位置及外部声明清单 |
| `source_audit.json` | 源码占位检查、外部公理白名单和未导入模块检查 |

源码审计扫描整个 `LittlewoodInverse/`，而非只扫描成功导入的部分。它剥除嵌套注释和字符串，拒绝 `sorry`、`admit`、`native_decide`、`sorryAx` 以及不在七项外部声明白名单中的公理；严格模式同时拒绝遗漏的正式模块。唯一排除项 `MomentCertificateTest` 是早期数值算术试验，不属于正文证明，也不进入交付包。

公开定理全部执行 `#print axioms`。私有辅助定理记录在声明清单中，其依赖由使用它们的公开定理递归覆盖。`Statements.lean` 中的 `Prop` 定义不计作已证定理。

定量主定理只依赖两项通用 Hardy/Poisson 输入；结构逆定理只依赖 MPS、BSG。Green–Sanders 只用于长块的有符号表示备注；两项 Bloom–Green 声明仅作背景比较。准确声明、来源和归一化见 `EXTERNAL_INPUTS.md`。数值证书、任意紧群 Sidon 引理、任意离散阿贝尔群遗传能量，以及双侧完成的最终渐近不依赖新增外部数学公理。

`propext`、`Classical.choice`、`Quot.sound` 是常规 Lean 基础依赖。外部数学公理按用户要求未在本工程内证明；构建通过不能证明这些公理本身。原稿与 Lean 陈述的对应关系及 δ 的条件澄清见 `PROOF_COVERAGE.md`。
