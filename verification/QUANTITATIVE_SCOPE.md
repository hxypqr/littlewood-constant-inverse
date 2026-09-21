# 定量常数部分及补充结论：已验证范围

本文档报告对称链、区间矩、sinc 极限、统一矩界、标量估计、外函数分析、数值证书和附录 B 所覆盖的范围。论文的定量主定理已由 `LittlewoodInverse.quantitative_theorem` 完整验证，包括实际误差级数给出的常数及其十进制下界。附录 B 的 Landau 尖锐界、零点排除、系数渐近及两侧相位补全也已完成。参照底稿为 `manuscript/Littlewood_constant_inverse.tex`。

这些模块均已由 Lean 4.32.0 编译通过，不引入内部自定义公理、`sorry`、`admit` 或 `native_decide`。外函数构造调用明确列于 `HardyExternal.lean` 的通用 Hardy 外部定理；其余内部分析、组合证明和有限精确数值计算均有 Lean 证明。

## 已完成的数学结论

下表使用模块名定位文件；声明位于 `LittlewoodInverse` 或其子命名空间。文件名不一定是声明的命名空间，例如 `LandauSpectral.lean` 的完整定理名是 `LittlewoodInverse.Landau.spectral_bound`，`CommonHeights.lean` 的定理直接位于 `LittlewoodInverse`。可在对应文件检索表中给出的声明末段名称。

| 稿件位置 | Lean 声明 | 已验证的内容 |
|---|---|---|
| 行 440–462，对称链引理 | `SymmetricChains.gridDecomposition`, `nonemptyGridDecomposition`, `grid_chains_saturated`, `nonempty_grid_antichain_card_le_middle`, `grid_rank_card_le_middle` | 完整构造实际有限格子的对称链分解：显式矩形编码与逆映射、乘积归纳、双射所保证的完整互不相交覆盖、秩逐步递增、相邻元素的 CovBy 饱和性。证明每个反链注入中央秩层，并证明中央秩层最大。 |
| 行 465–489，所有偶矩比较 | `IntervalMoments.relationCount_eq_zero_fiber`, `relationCount_le_middle`, `interval_relationCount_eq_middle`, `relationCount_le_interval`, `even_moment_le_interval` | 实际有限整数集的排序索引、后半索引反转、严格递增有符号和的零层反链、计数双射和区间中央秩层恒等式，最终证明任意偶数阶 Fourier 矩不超过等长区间矩。包含空集及零次幂情况。 |
| 第 3 节的字面多项式系数形式 | `IntervalCoefficients.geometric_power_coefficient`, `interval_relationCount_eq_coefficient`, `relationCount_le_coefficient` | 从有限多项式乘积展开证明中央格点数确实等于 `(1+X+⋯+X^(n−1))^(2r)` 的中央系数，完成稿件原式的精确识别。 |
| 行 490–492，尖锐能量公式 | `IntervalEnergy.pairSumCount_eq_interval`, `energy_eq_square_sum`, `three_mul_interval_energy`, `interval_energy_real`, `three_mul_energy_le`, `energy_max_real` | 显式计算区间每个二项和的表示数，通过平方和证明 `3 E(I_n)=2n³+n`；对所有实际有限整数集得到 `3 E(B)≤2 card(B)³+card(B)`。 |
| 四阶归一化矩及一致误差 | `IntervalEnergy.normalized_fourth_moment_eq`, `normalized_fourth_moment_le`, `normalized_fourth_moment_uniform` | 证明归一化四阶矩等于 `E(B)/card(B)³`，给出上界 `2/3+1/(3 card(B)²)`，并证明对所有整数集一致的 ε–N 版本。 |
| 行 509–518，区间重标度与 sinc 极限 | `SincMoments.scaledSincKernel_power_bound`, `integrable_sinc_power`, `tendsto_integral_scaledSincKernel`; `DirichletKernel.normalized_intervalPolynomial_eq_sinc`; `normalized_interval_moment_eq_scaledSinc` | 从实际几何级数证明 Dirichlet 核的正弦商恒等式；严格完成圆周 Haar 积分与实直线换元。用显式可积主函数 `5·2^k/(1+x²)` 证明截断 sinc 商的积分收敛到实际 sinc 积分。 |
| 行 495–502、517–520，一致归一化矩 | `UniformMoments.normalizedMoment_uniform`, `normalizedMoment_odd_sq_le`, `sincMoment_two`, `sincMoment_four`, `momentCoefficient_le_one`; `LittlewoodInverse.momentCoefficient_pos` | 证明每个整数阶 `k≥2`、任意 ε>0 存在对所有有限整数集共同的 N，使归一化矩不超过论文实际定义的 `c_k+ε`。包含奇数阶 Cauchy–Schwarz 插值；严格识别 sinc 积分 `I₂=1`、`I₄=2/3`，且 `0<c_k≤1`。严格正性在 `QuantitativeDetails.lean` 从连续被积函数在零点的值为 1 直接证明。 |
| 行 503–532，全部偶数 sinc 矩的精确公式 | `BoundedCompositions.card_composition`, `subtractThresholdEquiv`, `bounded_card_inclusion_exclusion`, `interval_relationCount_binomial`; `BinomialLimit.tendsto_choose_affine_div_pow`; `SincFormula.sincMoment_even_formula` | 通过 Sym 与弱分拆的实际双射证明 stars-and-bars 计数；通过逐坐标减阈值双射和有限容斥得到区间矩交替二项式公式。用有限乘积证明归一化二项式极限，再和实际积分极限的唯一性结合，完成所有 `r≥1` 的 sinc 偶矩确切有理数公式。 |
| 行 577–584，pointwise update | `outer_update_bound` | 实际复数的模长满足乘子模长预算时，更新后的模长不超过 1。乘子存在性和频谱性质不包含在本结论中。 |
| 行 632–671，whole-product algebra | `q_eq_one_sub_sq`, `q_mem_Icc`, `bonferroni_two`, `pairProducts_eq_half` | 有限列表上的二阶 Bonferroni 不等式、二次模长损失的定义和范围、交叉项与平方和的恒等式。 |
| 行 657–671 | `one_sub_exp_neg_le`, `whole_product_reduction` | 指数不等式，以及给定积分版 Bonferroni 前提后的实数代数化简。本条为标量归约；实际乘子和积分恒等式已在 `OuterDamping`、`WholeProduct` 和 `TailCoupling` 完成。 |
| 行 681–710 | `weighted_cauchy`, `coupled_tail` | 任意有限指标集合上的加权 Cauchy–Schwarz 与 coupled tail 代数不等式，允许总权重预算保留未使用的权重。 |
| 行 695–700、783–790 | `first_tail_weight`, `second_tail_weight`, `finite_geometric_weights`, `finite_weight_budget`, `higher_tail_weight_lower`, `tail_constant_algebra` | 特殊权重、有限几何级数、总权重上界、后续层权重下界，以及 $55a^2/108$ 的确切代数计算。 |
| 行 731–748，scalar large-b | `hasSum_logRemainder`, `logRemainder_mul_le`, `h_cubic_majorant`, `scalar_large_b_pointwise` | 对实际对数函数，证明其收敛幂级数余项的三次缩放上界；由此证明所有 $x\in[0,1]$、$b\ge11/8$ 时的完整点态不等式，包含 $x=0$。 |
| 行 744–748 | `log_ten_lt_five_halves`, `scalar_endpoint_negative` | 从指数 Taylor 部分和证明 $\log10<5/2$，进而严格证明所需端点差为负；这里没有把对数数值当作假设。 |
| 行 715–718，scalar large-b integral | `normalizedMagnitude`, `normalizedMagnitude_continuous`, `normalizedMagnitude_nonneg`, `normalizedMagnitude_le_one`, `normalized_second_moment`, `scalar_large_b_integral` | 对每个实际非空有限整数集 $A$，定义 $u=\lvert F_A\rvert/\#A$，证明其连续性、$0\le u\le1$、$\#A\int u^2=1$，并完整证明 $\#A\int(h_{.9}(u)+bq_{.9}(u)^2)\le(2+4b)(.9)^2$。这是稿件 scalar coupling 引理 large-b 分支的实际结论。 |
| 行 501–502、519–520 | `normalized_moment_le_one` | 对每个整数 $k\ge2$，证明实际指数和的通用有限上界 $\#A\int u^k\le1$。不包含 sinc 常数的渐近改进。 |
| 行 750–762 | `first_level_exact`, `first_level_pointwise_tail`, `first_level_pointwise` | 完整的一阶层多项式展开及非恒定主函数上界，保留真实对数余项或真实无限级数。 |
| 行 763–768 的换序部分 | `hasSum_tailFromFive`, `tailFromFive_eq_tsum`, `hasSum_integral_tail`, `normalized_integral_tail_eq_tsum` | 从 $k=5$ 开始的真实对数级数收敛性；以可求和常数函数作主函数，通过已证明的支配收敛定理严格交换级数与圆周积分。 |
| 行 719–727 的渐近代入之前 | `first_level_integral` | 对实际 $A$ 和 $0\le a<1$，证明 $b=1/3$ 时积分上界为 $10a^2/3+(5a^4/6-2a^3/3)\#A\int u^4+2\sum_{k\ge5}(a^k/k)\#A\int u^k$。其中所有积分、级数均为实际对象。 |
| 行 719–727、763–768，完整首层渐近结论 | `FirstLevelUniform.momentEnvelope`, `tendsto_weighted_envelope`, `first_level_uniform` | 对真实有限整数集、`a=9/10` 和 `b=1/3`，证明存在对所有集合共同的 N，使首层积分不超过 `10a²/3+Δ_a+ε`。无穷级数通过 Tannery 定理及独立于集合的可求和主函数严格控制。 |
| 行 1968–1974 的数值收尾 | `log_nine_upper`, `coefficient_gt_decimal`; `NumericalConstant.tailError_upper`, `littlewoodCoefficient_gt_sharp_decimal` | 从指数 Taylor 部分和严格证明对数有理包络；用实际 sinc 偶矩公式、奇数阶平方根包络、至 160 阶的精确有限求和及无穷尾项估计，证明真实误差级数上界及 $c_*>0.2459209213577253$。 |
| 定量主定理 | `LittlewoodInverse.littlewood_asymptotic`, `LittlewoodInverse.quantitative_theorem` | 实际外乘子、初始段链和统一误差预算组合为对所有足够大的有限整数集一致成立的渐近下界，并与实际常数的十进制下界结合。 |

大权重分支使用与原文等价的级数论证：设 $R(y)=-\log(1-y)-y-y^2/2$，由每个 $k\ge3$ 的 $x^k\le x^3$ 得 $R(ax)\le x^3R(a)$。这避免在 $x=0$ 处对 $h(x)/x^2$ 作形式上的除法，同时保留原文的完整结论。

## 模块整合状态

1. **第 3 节的有限组合部分现已全部完成。** 对称链、反链中央秩层界、实际偶矩计数、所有偶矩区间比较、尖锐有限能量公式及字面生成多项式系数表示均已完成，不再是缺口。
2. **第 3 节的一致矩渐近与确切公式现已完成。** 实际区间矩趋于 sinc 积分、奇数阶相邻偶矩插值、全部固定整数阶的一致 ε–N 界，以及所有 `r≥1` 的 `I_{2r}` 有限交替二项式公式均已完成，不再是缺口。
3. **Outer damping 引理已在其他模块完成。** `OuterDamping.lean` 借助 `HardyExternal.lean` 中两条明确记录的通用 Hardy 外部定理，构造精确指定模长的 M；乘积 Fourier 支撑、常数项与平均值在项目内部证明。此处不再把外函数存在性记为内部缺口，外部依赖仍须查阅总审计表。
4. **Initial-segment pairing 引理已完成。** `PrefixPairing.initial_segment_pairing_error` 处理实际 L² 乘子、非正 Fourier 支撑和尖锐半能量估计，不再是缺口。
5. **Whole-product 分析不等式及实际链实例化均已完成。** `WholeProduct.estimate` 在一般 AE 可积框架下证明完整 Bonferroni 积分估计；`TailCoupling.outer_product_coupled` 将实际外乘子及其链乘积代入，并内部证明全部技术假设。
6. **Scalar coupling 两个分支现已完成。** 大权重分支为 `ScalarCoupling.scalar_large_b_integral`；首层分支为 `FirstLevelUniform.first_level_uniform`，后者已经严格处理实际矩的统一渐近及无穷级数换序，不再是缺口。
7. **Uniform tail budget 与定量主定理均已完成。** `uniform_outer_tail_budget`、实际初始段链及其长度渐近、对偶配对已组合为 `LittlewoodInverse.littlewood_asymptotic`，证明对所有足够大的有限整数集一致成立的 ε–N 形式。`LittlewoodInverse.quantitative_theorem` 将此结论和实际常数下界结合。
8. **附录 A 的有限数值证书已完成。** `EvenMomentCertificate` 验证至 162 阶的实际 sinc 偶矩有理数值；`CoefficientValues` 与 `CoefficientBounds` 验证 5 至 160 阶系数的 24 位向上包络。`MomentCertificate.finite_error_bound` 的精确有理数计算与 `SeriesCertificate.momentSeries_le_finite` 的真实无穷尾项结合，得到 `NumericalConstant.tailError_upper`。随后证明 `littlewoodCoefficient_gt_decimal` 及更强的 `littlewoodCoefficient_gt_sharp_decimal`：实际常数大于 `0.2459209213577253`。全部有限算术经 `norm_num` 构造内核检查的证明，未使用 `native_decide`。
9. **附录 B 已完成。** 下述 `Landau.*` 声明均位于 `LittlewoodInverse.Landau` 命名空间。`Landau.spectral_bound`（`LandauSpectral.lean`）证明实际可测有界测试函数的精确频谱上界。`Landau.polynomial_ne_zero_closedDisk`、`Landau.extremizer_support`、`Landau.extremizer_attains`（`LandauSharpness.lean`）证明闭单位盘内无零点、极值函数的频谱条件与等号。`Landau.sum_b_sq_log_error`（`LandauAsymptotic.lean`）从 Wallis 恒等式与调和数界内部证明系数平方和与 `log N / π` 相差至多 2。`Landau.b_sq_asymptotic_error`（`QuantitativeDetails.lean`）还给出逐项误差 `|b_n²−1/(πn)|≤1/n²`，无须添加 Stirling 公理。`LandauBoundary.lean` 内部证明实际边界级数收敛、Abel 尾项与平方恒等式。`PhaseNormalization.lean` 和 `Landau.completionError_integral_le`（`LandauCompletion.lean`）证明相位扰动和积分误差至多 192。`Landau.completion_log_asymptotic`（`LandauResults.lean`）给出完整两侧补全渐近；所需 Dirichlet 范数渐近也由 `LittlewoodInverse.dirichlet_l1_asymptotic`（`IntervalAsymptotic.lean`）内部证明。

## 对原文条件的最终语义核查

- `LittlewoodInverse.QuantitativeTheorem`（`Statements.lean`）的 `sincMoment`、奇数阶几何平均系数、`tailError` 和 `littlewoodCoefficient` 与原文公式逐项一致。量词是先给 ε，再选统一的 N₀，之后适用于每个足够大的有限整数集；没有集合直径或额外正则性假设。
- 第 6.1 引理的 `Majority.majorityDegree T` 定义为 `2 * ceil((64 T² − 1)/2) + 1`。`majorityDegree_odd`、`majorityDegree_lower` 和 `majorityDegree_minimal` 共同证明它是原文要求的**最小**奇数，而非较大的替代值。`dense_mixed_correlations` 允许任意有限索引类型；被计数的两段有序元组经 `Fin.append` 恰为所有指标互异的有序元组，前段长度比后段多 1。相关阈值和数量阈值使用同一个绝对常数 300。输入范数上界 `∫‖F‖ ≤ Tκ` 可直接取原文的 `T=‖F‖₁/κ`。
- 第 5.1 引理的 `PeelingPolynomial.lean` 中，`LittlewoodInverse.hereditary_energy_cover_polynomial` 显式吸收原来额外的 δ 因子，给出原文所写的同一个绝对指数：块大小 `≥cη^Cδ^C|X|`，块数量和倍增常数 `≤Cη^(-C)δ^(-C)`。`c,C` 在任意交换群以及 `X,η,δ` 之前选取，不依赖后者。
- 第 10 节关于初始段阈值的文字“固定 δ>0，再令 M 足够大”需要限定 `δ<1`，因为其论证使用 `M^(1−δ)→∞`。`ParameterObstructions.prefix_threshold_eventually_ge_fibres` 明确要求 `δ<1`。这与引言中所引用结果的 `δ≤1/2` 一致；对于 `δ≥1`，原文字面论证不成立，不能声称已证明该更广陈述。
- 第 10 节二次参数障碍已经直接对应实际集合：`interlacedSet_low_norm`、`interlacedSet_energy_size_cost`、`interlacedSet_doubling_cost` 和 `initial_segment_parameter_obstruction`，并非仅对抽象参数作代数假设。
- `LittlewoodInverse.uniform_cover_iff_macroscopic_energy`（`QualitativeEquivalence.lean`）保留统一集合族中的阈值与常数量词；`LittlewoodInverse.repeated_model_norm_transport`（`RepeatedModels.lean`）对任意两个重复高阶模型证明范数差 `<2/π`，不随模型更换次数累积。
- `CommonHeights.lean` 给出实际非零边界高度集合、MPS 高度数量界与每个实际残余切片的谱预算。`LittlewoodInverse.aspect_boundary_budget`（`AspectBoundary.lean`）给出一般 `0<σ≤1/2` 和 `M≥V^(1/2+σ)` 的明确结论 `S≤4πK/σ`，大基数阈值也显式给出。
- `LittlewoodInverse.cyclic_coset_normal_form`（`CyclicCosetNormalForm.lean`）内部证明循环群任意子群陪集的规范除数/余数表示，供 Green–Sanders 外部定理的精确循环群实例化使用。`LittlewoodInverse.discreteEvaluation_injective`（`DiscreteCharacters.lean`）内部证明任意离散交换群进入双对偶的实际评价映射单射，消除一般交换群谱论陈述中的字符分离假设。
- `LittlewoodInverse.compact_freiman_integral_even_moment`（`CompactFreimanMoments.lean`）证明任意两个交换群之间 Freiman 同构所保留的全部指定阶偶矩。两侧都是实际紧交换群上的 Fourier 多项式与归一化 Haar 积分；矩计数来自内部证明的字符正交性。此桥梁不要求频率群是整数群，也不假设两侧矩相等。

## 独立数学审查与数值重算

已逐行审查定量部分和两个附录，未发现可确认的错误代数步骤或反例。此审查不是形式证明。

原始包中的 `verify_constant.py` 已独立运行，全部精确有理数断言通过，给出：

- `E_upper = 0.4790844570202558609421346390638101925968`
- `c_lower = 0.2459209213577253716084341310173096308610`
- `endpoint_difference_upper = -1.112192314011908631964017090631271584798`

Python 仅生成候选有理数；正式交付使用独立的 Lean 证明检查全部系数、平方根包络、有限和与无穷尾项，不依赖 Python 输出的正确性。

## 复验

在项目根目录运行 `lake build LittlewoodInverse.QuantitativeTheorem`，会验证实际定量主定理、有限数值证书及其全部内部分析和组合依赖。首次精确数值证书构建需要数分钟；后续缓存构建较快。项目整体的公理依赖检查由 `verification/axioms.log` 单独记录。
