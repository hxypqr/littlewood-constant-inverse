# 手稿语义与证明范围复核

本复核将可编译性、数学依赖和与原稿结论的匹配分别检查。仅有定义或带有待证前提的归约不算原命题证明。最终状态以总构建和公理审计日志为准。

## 主定理与定义

- `Statements.QuantitativeTheorem` 的常数是实际 sinc 积分和无限尾级数定义的 `littlewoodCoefficient`；数值结论没有替换该常数。渐近阈值在所有目标有限整数集之前量化。
- `Geometry.DenseBlocks` 保留每个块的统一直径、逐块下界、原集合幂次密度和严格分离。`Assembly.node` 的原集合就是全部非空孩子的准确并集；没有省略非 Sidon 的其余支撑。
- `Terminal.inflation` 使用真实循环余数和整数高度，保留正膨胀长度、非空单元集及单元数不超过膨胀长度的假设。
- `StructuralInverseTheorem` 的常数及阈值仅依赖 `K, ε, β, Δ`，先于集合及其分解选择。`AdmitsAssemblyModel` 的模型使用阶数为原集合基数的真实 Freiman 同构。
- `AlmostCover` 同时包含目标子集性、非空性、线性基数、倍增、互不相交、遗漏质量与片数界。没有只证明一个较弱的单块结论。

## 局部证明与变更

- Fourier 函数、积分、能量和关系计数均为具体定义。外部输入没有抽象掉手稿内部的 Fourier 矩恒等式。
- 多数放大使用实际 Boolean 展开、相位积分、子集双计数和互异有序元组。中间采用 `2^m` 的系数质量上界，配合更宽的绝对常数，得到同一指数密度结论。这是证明路线的加强常数调整，不是把欲证密度作为假设。
- 标签能量的进位关系通过原始证书及目标频率支撑推出；标签提升回原块的损失明确计入覆盖参数。
- 边界提取、公共高度、有限残余谱与整数 slab 都使用原始整数系数。Green–Sanders 备注的提升是有符号等式，允许抵消；没有错误地附加等差数列长度受目标基数控制的结论。
- 附录 B 的 `completion` 正是 `phase(Q/conj Q + z^(N-1)*conj(Q/conj Q))`，分母为零处取零。Landau 谱界、尖锐测试、Wallis 渐近、边界级数尾界和配对损失均有证明。`completion_log_asymptotic` 仅依赖 Lean 基础公理；没有引入 Dirichlet 渐近公理。
- 初始段参数障碍的解释必须取 `δ<1`，使 `N^(1-δ)` 随 `N` 增长。`ParameterObstructions.prefix_threshold_eventually_ge_fibres` 明确指出并使用这一条件；原稿该处孤立的“固定 δ>0”应理解为前文的适用参数范围。

## 广度检查

只在整数或循环群上证明的版本不足以覆盖原稿第 5.2、8.1 和 9.2 项的一般群陈述。因此另设：

- `CompactCharacters`：任意紧阿贝尔群上的实际连续角色族，概率 Haar 正交性和矩恒等式。
- `DiscreteCharacters`：任意离散阿贝尔群到其双 Pontryagin 对偶的实际单射评价映射，内部证明角色分离。
- `CompactHereditary`：一般角色族遗传能量，以及在离散群实际紧对偶上的规范 Haar 特例。
- `CompactSidon`：已完成原稿完整紧群 Sidon 结论，包括字面实数二十分之一次幂形式。`CompactFreimanMoments` 和 `CompactTransport` 已完成跨群实际矩保持与精确 Chebyshev 范数转移；`CompactFreiman` 将其接到两个任意离散阿贝尔群的规范紧对偶。最终覆盖仍须与总构建核对，不能用旧的循环群/整数特例代替。

## 审计器

`generate_audit.py` 从总入口递归计算本项目导入闭包，同时扫描整个源码目录。它报告七个许可外部公理以外的声明、禁用证明占位符和未导入模块。`--strict` 遇到任一问题即失败；唯一明确排除的生成测试模块为 `MomentCertificateTest`。

源码扫描是辅助检查，不能自行证明定理陈述忠实，也不能替代 Lean 内核。`AuditAll.lean` 对公开定理逐一运行 `#print axioms`；私有辅助定理随依赖它们的公开结果被审计。扫描器包含注释、字符串、缩进公理和声明修饰符的回归检查。

## 逆定理部分的独立逐项复核

- 原稿第 182–300 行与 `Statements`、`Geometry` 对照：数值阈值、参数范围、模型阶数、集合之前的统一常数量词及覆盖全部条件一致。额外允许任意非零整数仿射变换与原稿逐节点归一化等价；构造的孩子全部非空，模数剩余类互不相交，因此 `Assembly.node` 精确保留完整剩余支撑。没有关于深度、分支数、模数或整数直径的隐藏上界。
- 原稿第 1210–1303 行的两个边界结论分别对应 `BoundaryExtraction.uniform_boundary_extraction` 与 `BoundaryAsymptotic.boundary_asymptotic_explicit` / `boundary_norm_asymptotic`。后者的误差常数只依赖固定的单元集与模数，确实独立于膨胀长度。`IntervalAsymptotic.boundaryNorm_single_cell` 明确算出单元边界范数 `4/π`，据此内部推出区间的 `4/π²` 渐近；它不是新的外部输入。
- 原稿第 1462–1522 行的一般紧群 Sidon 引理已由 `CompactSidon.compact_dual_sidon_constant_one` 直接覆盖，角色就是任意紧阿贝尔群的 Pontryagin 对偶元素。概率 Haar 正交性、二次和四次矩先从角色平移与 Sidon 条件证明，最后应用内部解析不等式；没有把欲证矩性质变成未证明的假设。
- 原稿第 1773–1827 行的 Sidon fibres 命题由 `SidonFibreExamples.sidon_fibres` 及其具体 `interlacedSet` 实现。余数是实际三的幂，模数为 `3^R`；基数、范数、任意子集能量、初始段能量及完整装配证书都已连接。初始段计数实际上得到常数 `4` 的更强中间式，再推出稿中常数 `16`。
- 原稿第 1838–1852 行个别 fibre 的精确能量 `(2M³+M)/3` 和基数 `M` 由 `interlacedSet_individual_fibre` 明确记录。`ParameterObstructions` 证明 `Q≥cR/2`、子集能量的尺寸成本及任意 `p<2` 的初始段参数障碍。第 1832–1834 行孤立的“固定 δ>0”需要补充 `δ<1`：当 `δ≥1` 时，所写阈值不随 `N` 增长，原句字面上不成立。正式结果公开保留正确范围，而不声称证明错误的全范围句子。
- 原稿第 1854–1886 行的深度例子由 `UnboundedDepthExamples` 实现。`unbalancedSet_fibre_recursion` 是每一步真正的 `{0,1}⊆ZMod 3` 分解；`logarithmicChainDepth_tendsto` 及 `logarithmic_chain_low_norm` 证明深度参数无界且范数仍为对数级。完整三进制数字集有显式数字表示、精确基数 `2^h`、`1/20` 次幂范数下界和最终超过任何固定对数界的结论。

这些项目以已列出的命题及其实际依赖为准；证明采用等价的有限计数或更强常数时，不要求逐字重复手稿中的中间计算。

