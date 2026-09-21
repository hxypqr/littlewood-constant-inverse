# 证明覆盖清单

状态：**全文内部数学结果已给出 Lean 证明，包括两个主定理、一般群版本、应用、例子和两个附录。**
下表对应固定原稿，区分内部证明与外部陈述。

| 原稿结果 | Lean 模块 | 当前状态 |
|---|---|---|
| 1.1 显式 Littlewood 常数主定理 | QuantitativeTheorem, NumericalConstant | **完整证明**：实际 c_* 的统一渐近下界及 c_*>0.2459209213577253>0.2459209 |
| 1.2–1.4 精确几何与装配类 | Geometry | 完整具体定义，保留全部几何、模数、密度假设 |
| 1.5 结构逆定理 | ModelReduction, AssemblyReduction, TerminalCover | **完整证明**：实际任意深度装配及高阶模型，全部终端输入已证明并接通 |
| 1.6 宏观遗传能量 | CoverEnergy, MacroscopicEnergy, Corollaries | **完整证明**，所有统一量词与主结构定理应用均已接通 |
| 第 2 节 Fourier 初等性质 | Fourier, NormBounds, ResidueProjection | 实际矩、配对、仿射不变、范数界和 residue projection 完整 |
| 2.1 MPS、2.2 BSG | External | 两项准确外部声明，来源见 EXTERNAL_INPUTS.md |
| 3.1 对称链 | SymmetricChains | 实际有限格子的完整对称链分解、饱和性、反链中央层界 |
| 3.2 全部偶矩比较 | MomentCounting, IntervalMoments, IntervalCoefficients | 完整，包含原稿字面生成多项式系数形式 |
| 3.3 统一归一化矩和 sinc 精确公式 | IntervalEnergy, DirichletKernel, SincBridge, SincMoments, UniformMoments, SincFormula | 全部完成；奇阶插值、积分极限及全部偶阶精确公式均已证明 |
| 4.1 外阻尼 | OuterDamping, OuterFamily | 从一般 Hardy 外部输入内部构造实际乘子；模长、谱支撑、均值、乘积性质完整 |
| 4.2 初始段配对 | PrefixCount, PrefixPairing | 完整精确单侧误差常数，对实际 L² 乘子成立 |
| 4.3 整体乘积误差 | WholeProduct, TailCoupling | 完整函数空间积分证明，乘积模长和均值前提均由实际外函数性质推出 |
| 4.4 标量耦合 | ScalarCoupling, FirstLevelUniform | 两分支和第一层统一渐近全部完成 |
| 4.5 统一尾预算 | TailWeights, UniformTailBudget | 对实际频率集和任意有限尾长度的统一结论完整 |
| 第 4 节定量主定理组装 | DampedTest, PrefixChain, GeometricAsymptotic, QuantitativeAsymptotic | 完整；最终 quantitative_theorem 已构建并进行公理审计 |
| 5.1 BSG 反复提取 | Peeling, PeelingPolynomial, HereditaryCover | 完整；绝对常数在群、集合、参数之前量化，包含原稿统一指数的字面多项式界 |
| 5.2 谱预算到遗传能量 | SpectralEnergy, CyclicSpectral, CompactCharacters, DiscreteCharacters, CompactHereditary | 完整任意离散阿贝尔群的真实紧对偶版本；评价特征单射、归一化 Haar 和正交性均内部构造证明，并包含整数、循环群实例 |
| 6.1 多数混合相关 | BooleanMajority, MajorityAmplification, MajorityPhase, MajorityBlocks, MajorityCounting, MajorityFactorial, MajorityOrdered, DenseMajority | 完整；实际有序互异元组，明确绝对常数 300 |
| 6.2 有限带证书 | FejerKernel, FiniteBand, PacketCertificates | 完整实际多项式、频谱、L∞ 界及对完整原目标的精确配对 |
| 6.3 标签遗传能量 | PacketSupport, PacketEnergy, PacketRelations | 完整；实际有序相关注入进位关系计数，明确指数常数 2000 |
| 6.4 稠密分离块覆盖 | PacketGeometry, LabelGeometry, PacketBudget, PacketLift, DenseCover | **完整统一覆盖定理**，所有五项覆盖条件均证明 |
| 7.1 边界提取及固定模型渐近 | BlockBoundary, BlockBoundaryIntegral, PeriodicBounds, PeriodicHarmonic, BoundaryExtraction, BoundaryAsymptotic | 完整实际整数边界、统一提取，以及固定 q、C 的有界误差渐近 |
| 7.2 常数边界预算 | BoundaryExtraction, AspectBoundary | 完整；包括一般 M≥V^(1/2+σ)、0<σ≤1/2 下 S≤4πK/σ 的参数版本 |
| 7.3 公共高度 | CommonHeights | 完整：实际非零整数边界、MPS 高度计数及全部残余谱预算 |
| 7.4 进位提升 | CarryLift | 完整实际整数 slab，两个进位均保留 |
| 7.5 长块覆盖 | BlockSlabs, SlabCover, FiniteCoverGluing, LongBlockCover | **完整统一覆盖定理**：真实分片、公共高度、循环谱覆盖、整数提升和有限覆盖拼接全部接通 |
| 第 7 节额外有符号表示备注 | GreenSandersCyclic, CyclicCosetNormalForm, GreenSandersProgressions, CosetLift, SignedProgressions, LongBlockSigned | 完整；一般 Green–Sanders 是外部输入，实际循环范数识别、陪集标准形、单进程提升和全部分片拼接内部证明 |
| 8.1 常数一 Sidon 聚合 | SidonAlgebra, SidonAnalytic, CyclicSidon, CompactCharacters, CompactSidon | 完整任意紧阿贝尔群对偶中的 Sidon 集版本，包含原式二十次方根；实际 Haar 正交性与矩恒等式均已证明 |
| 8.2 fibre / 叶预算 | FibreBudget, AssemblyBudget, RetainedLeaves | 实际 Fourier fibre、集合树、深度无关预算、叶质量渐近全部完成 |
| 第 8 节全树覆盖组装 | CoverGluing, AssemblyReduction, TerminalCover | 完整证明，统一终端覆盖输入已经接通 |
| 第 8 节定性等价备注 | QualitativeEquivalence | 完整；统一几乎覆盖与每个固定密度的统一遗传能量等价，保留大小阈值 |
| 9.2 高阶 Freiman 模型范数转移 | FreimanMoments, PolynomialTransport, SineFourier, ChebyshevTransport, CompactFreimanMoments, CompactTransport, CompactFreiman, CoverFreiman, ModelReduction | 完整任意离散阿贝尔群之间的版本；真实紧对偶的偶矩保持、精确 Chebyshev 尾误差、所有子集范数转移、能量和和集保持均已证明 |
| 第 9 节反复模型变更备注 | RepeatedModels, CompactFreiman | 完整；任意长整数复合映射及任意大小、不同离散群中的模型族，任意两个阶段直接比较，误差不随模型次数累计 |
| 9.3 小异常扰动 | NormBounds, PerturbationCover, PerturbationAsymptotic, Corollaries | **完整证明**，有限稳定性、渐近量词和主结构定理应用全部接通 |
| 10.1 Sidon fibres 例子 | SidonFibreExamples, IntervalNorm | 完整实际三进制构造、基数、范数、所有子集能量、初始段能量及装配成员性 |
| 第 10 节参数障碍 | ParameterObstructions | 完整；大块倍增代价、能量大小代价、p<2 的低范数反例族和宏观前缀阈值 |
| 第 10 节无界深度例子 | UnboundedDepthExamples | 完整；深度 floor(log M)^2 趋于无穷的低范数链，以及完整二叉分支最终违反任意固定 K log N 界 |
| 附录 A 精确证书 | BoundedCompositions, BinomialLimit, EvenMomentCertificate, CoefficientValues, CoefficientBounds, MomentCertificate, SeriesCertificate, SharpLogBounds, NumericalConstant | 实际积分到精确有理数证书全部完成；数值结论仅依赖 Lean 基础公理 |
| 附录 B Landau 不等式与尖锐性 | LandauCoefficients, LandauSpectral, LandauSharpness, LandauAsymptotic | 完整；实际谱类、系数卷积、闭盘无零点、显式极值函数，以及系数平方和与 log N/π 相差至多 2 |
| 系数正性及逐项渐近 | QuantitativeDetails | 完整；所有 k≥2 的实际 sinc/插值系数严格为正，Landau 系数满足显式 O(n^-2) 误差 |
| 附录 B 单侧递归端点限制 | OuterEndpoint | 完整；实际区间子集来源和实际 DampingData 自动满足谱限制，最终配对≤log N/π+2 |
| 附录 B 双侧 completion | LandauBoundary, LandauModel, PhaseNormalization, LandauCompletion, IntervalAsymptotic, LandauResults | 完整；实际边界级数、Abel 尾、相位恒等式、统一误差 192 和 4/π² 的有界误差渐近，Dirichlet 渐近也内部证明 |

## 信任边界

显式外部数学声明共七项：一般 MPS、BSG、两项通用 Hardy/Poisson 边界输入、一般 Green–Sanders，以及两项 Bloom–Green 背景比较。定量主定理仅用两个 Hardy 输入；结构逆定理仅用 MPS、BSG。Green–Sanders 只用于额外表示备注，Bloom–Green 不用于内部证明。数值证书和双侧完成的最终渐近只依赖 Lean 基础公理。

源码与依赖审计排除内部公理、证明占位和未经证明的本机求值。最终声明清单、原稿对应关系和依赖日志分别承担不同的核查作用，不能互相替代。

## 原稿中的条件澄清

第 10 节在 `N=RM`、固定 R 时，把 `N^(1−δ)` 级别的前缀长度通过增大 M 保证为至少 R。这一步需要 **0<δ<1**；原文写“固定 δ>0”时省略了此上界。`ParameterObstructions.lean` 明确加入必要条件。两个主定理的陈述不受影响。

证明采用等价或更强的论证，不要求逐行复制原稿。例如 Landau 系数渐近由 Wallis 界内部证明，多数引理使用足够的较粗中间估计但保留原引理相同的假设和结论。历史综述、开放问题和“本证明不能推出什么”的讨论不登记为已证数学定理；引文用途见 `BIBLIOGRAPHY_AUDIT.md`。

## 原稿固定

PDF 与 LaTeX 来自用户 ZIP 的 `paper_versions_20260917/06_Littlewood/`。

```text
LaTeX SHA256 D3518604BF21C0AEDB87997319D8CB315217FA958B1F10AB14521D20463C5483
PDF   SHA256 CDF7B61EF18EA63884BEE6113DFD973D7C15AB1CA04BE9FB0A6CC0F19093F0D3
```


