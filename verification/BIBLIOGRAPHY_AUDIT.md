# 引文与形式化范围核对

核对对象为原稿所有 `\cite` 所在位置。引文承担的角色不同：实际外部证明输入、另有内部证明的经典事实、背景比较，以及历史或问题描述。历史引文不能自动成为一个新的数学假设；原稿自己证明的命题也不能通过引用文献来跳过。

| 原稿引文 | 实际用途 | Lean 处理 |
| --- | --- | --- |
| MPS；Hanson Theorem 1.1 | 加权 Littlewood 不等式的实际输入 | `External.mps_weighted`；集合的对数下界在 `MPSConsequences.lean` 内推导 |
| Tao–Vu Theorem 2.31；Reiher–Schoen | 多项式 BSG | `External.polynomial_bsg`；差集原定理与和集推论的区别见 `EXTERNAL_INPUTS.md` |
| Duren | 通用 Hardy/Poisson 径向边界理论 | `HardyExternal` 中两个精确通用陈述；乘子的构造、精确模长和乘积估计内部证明 |
| Green–Sanders | 有限群整数函数的有界符号陪集表示；第 7 节额外备注 | `BackgroundExternal.green_sanders`；实际有限 Fourier 代数范数已定义，循环群范数识别与整数等差数列提升另作内部证明 |
| Bloom–Green | 无条件初始段能量基准与历史常数比较 | `BackgroundExternal.bloom_green_inverse` 与 `bloom_green_constant`；常数使用原文精确二变量表达式，不把小数截断当成精确最优值；两条都不是本项目主定理输入 |
| Gabriel；Hardy–Littlewood | 离散重排或矩极值的历史来源 | 原稿提供的有限反链/链分解证明在本项目内部实现；没有新增重排公理 |
| de Bruijn–van Ebbenhorst Tengbergen–Kruyswijk | 对称链分解来源 | `SymmetricChains.lean` 显式构造与证明，不作为外部公理 |
| LandauAsymptotics；Kovalev | 附录 B 的经典背景 | `LandauCoefficients`、`LandauSpectral`、`LandauSharpness`、`LandauAsymptotic` 给出内部证明；渐近用 Wallis 界，不需要 Stirling 或 Landau 渐近公理 |
| Zygmund | 等差数列 Dirichlet 核范数的标准渐近及强 Littlewood 问题的背景 | `IntervalAsymptotic.lean` 从已证明的边界渐近内部推出精确区间范数渐近；不把强 Littlewood 猜想当作定理 |
| Konyagin | Littlewood 猜想独立证明的历史归属 | 所需同量级下界已经从加权 MPS 陈述内部推出；不重复添加另一个等价输入 |
| Stegeman；Yabuta；Fournier | 历史数值改进和有界测试函数方法综述 | 不是本文证明输入，没有把综述或十进制历史报道整体公理化 |
| Petridis；Hanson | 真正多维结构的既有研究背景 | 本文没有调用它们的多维定理来代替任何内部步骤；Hanson 被实际使用的精确 MPS 陈述已单列 |
| Pichorides；Bedert | 最大 dissociated 子集及模型大小的已有研究背景 | 不属于本文实际证明输入；本项目对参数依赖和模型传递的内部论证另行证明 |
| Bourgain；Bedert | 大无和子集问题的历史联系 | 仅背景联系，没有被当作本文的数学假设 |

原稿提到的强 Littlewood 猜想和 signed-progression 猜想均为开放问题的描述，不能登记成外部定理或公理。Green–Sanders 的有符号表示允许大等差数列相互抵消，因此不能将它误写成每个等差数列长度受原集合基数控制的猜想结论。

实际查验的外部结果原始文本及归一化说明集中记录在 `EXTERNAL_INPUTS.md`。本表区分引文角色，并不声称逐页核验了所有仅作历史背景的原始出版物。

