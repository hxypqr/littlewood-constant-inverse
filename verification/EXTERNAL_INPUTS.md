# 外部结果与信任边界

核对日期：2026-09-17。对应手稿：`manuscript/Littlewood_constant_inverse.tex`。

本项目一共显式声明七个外部数学公理。两个主定理使用其中四个输入：前两个位于 `LittlewoodInverse/External.lean`，后两个位于 `LittlewoodInverse/HardyExternal.lean`。另在 `BackgroundExternal.lean` 单独陈述三个背景比较及 Green–Sanders 备注所用的定理，避免将它们混入主定理的信任边界。

| Lean 名称 | 外部结果 | 使用范围 |
| --- | --- | --- |
| `LittlewoodInverse.External.mps_weighted` | McGehee–Pigno–Smith 加权 Littlewood 不等式 | 任意递增整数频率及任意复系数 |
| `LittlewoodInverse.External.polynomial_bsg` | 多项式 Balog–Szemerédi–Gowers 定理的和集形式 | 任意阿贝尔群中的非空有限集 |
| `LittlewoodInverse.HardyExternal.schwarz_integral_boundary` | Schwarz–Poisson 积分的解析性、实部范围与几乎处处径向边界值 | 任意实值 `L∞` 圆周数据 |
| `LittlewoodInverse.HardyExternal.bounded_holomorphic_radial_boundary` | 有界全纯函数的 Fatou 边界定理及 Cauchy/Fourier 系数识别 | 单位圆盘上任意有界全纯函数 |
| `LittlewoodInverse.BackgroundExternal.green_sanders` | Green–Sanders 定量幂等定理的有限群版本 | 有界 Fourier 代数范数的整数值函数；仅额外表示备注 |
| `LittlewoodInverse.BackgroundExternal.bloom_green_inverse` | Bloom–Green 初始段能量逆定理 | 原稿背景比较；不是主定理输入 |
| `LittlewoodInverse.BackgroundExternal.bloom_green_constant` | Bloom–Green 精确二变量常数表达式的渐近下界 | 原稿背景比较；不是主定理输入 |

这些公理按用户许可只给出陈述，不包含 Lean 证明。它们不是手稿主定理的替代品；主定理、内部引理和原文包含证明的命题不能仅因附近有参考文献就改作公理。

## 1. 加权 McGehee–Pigno–Smith 不等式

**核对来源：**

- 原论文：O. C. McGehee、L. Pigno、B. Smith，*Hardy's inequality and the L¹ norm of exponential sums*，Annals of Mathematics 113 (1981)，613–618，[DOI](https://doi.org/10.2307/2007000)。原论文 Theorem 2 的全文可在 [Kansas State University 保存的 Pigno 文献合辑](https://www.math.ksu.edu/about/awards-history/history/historical_materials_additional/L_Pigno_collection-merged-compressed.pdf)中核对。
- 手稿指明的显式复系数版本：[Hanson，arXiv:2003.01561v2，Theorem 1.1](https://arxiv.org/html/2003.01561v2)。该研究论文直接给出任意复系数、递增整数频率和绝对正常数的形式。

Lean 陈述选取一个绝对常数 `c > 0`，对每个 `m : ℕ`、每个严格递增的 `n : Fin m → ℤ` 及每个 `u : Fin m → ℂ`，要求

\[
c\sum_{j=0}^{m-1}\frac{|u_j|}{j+1}
\le \int_{\mathbb R/\mathbb Z}\left|\sum_{j=0}^{m-1}u_j e(n_jt)\right|\,dt.
\]

`Fin m` 从零编号，故分母为 `j.val + 1`。系数可以为零；`m = 0` 给出成立的空和特例。积分使用总质量为一的 Haar 测度。原论文 Theorem 2 的常数位于另一边，取其倒数即得到这里的 `c`。本项目没有假设任何优化后的数值常数。

## 2. 多项式 Balog–Szemerédi–Gowers 定理

**核对来源：**[Reiher–Schoen，arXiv:2308.10245v2，Theorem 1.2](https://arxiv.org/html/2308.10245v2)，发表于 Combinatorica 44 (2024)，691–698，[DOI](https://doi.org/10.1007/s00493-024-00092-5)。论文开头将 additive set 明确定义为任意阿贝尔群中的非空有限集。手稿另引用 Tao–Vu，*Additive Combinatorics*，Theorem 2.31；本次直接核对的全文是 Reiher–Schoen。

Reiher–Schoen 的原陈述给出**差集**控制：对于 `K ≥ 1` 及固定 `0 < ε < 1/2`，从 `E(Y) ≥ |Y|³/K` 提取 `Z ⊆ Y`，使

\[
|Z|\ge(1-\varepsilon)K^{-1/2}|Y|,
\qquad |Z-Z|\le 2^{33}\varepsilon^{-9}K^4|Z|.
\]

本项目的公理是其标准的多项式**和集**推论，不把原论文误写为和集原陈述。固定例如 `ε = 1/4`，再用标准和差集不等式，即得本项目使用的形式。令 `K = 1/γ` 并放大绝对常数及指数，可统一写成：存在绝对 `c,C > 0`，使

\[
E(Y)\ge\gamma|Y|^3,\quad 0<\gamma\le1
\quad\Longrightarrow\quad
\exists\varnothing\ne Z\subseteq Y:
\ |Z|\ge c\gamma^C|Y|,
\ |Z+Z|\le C\gamma^{-C}|Z|.
\]

`c,C` 的存在量词位于群 `G`、集合 `Y` 和参数 `γ` 的全称量词之前。Lean 中 `G` 仅要求 `AddCommGroup` 和可判定相等；没有有限群或拓扑假设。实数幂使用 `Real.rpow`。能量是 `Finset.addEnergy Y Y` 的实际整数计数，不是一个由假设规定性质的抽象函数。

## 3. Hardy 空间与 Poisson 边界定理

手稿 Lemma 4.1 明确引用 Duren 的标准 Hardy 空间边界收敛理论。这里仅将通用边界定理作为外部输入，内部构造仍然由 Lean 证明。

**可核对的来源：**

- Axler、Bourdon、Ramey，*Harmonic Function Theory*，第二版，[作者提供的完整 PDF](https://www.axler.net/HFT.pdf)：Proposition 1.20 给出 Poisson 核的正性和积分为一；Theorem 6.39 给出任意 `L¹` 边界数据的 Poisson 积分几乎处处非切向收敛。本项目只使用其较弱的径向结论，区间界是正核平均的直接标准推论。
- Auberson、Epele、Mahoux、Simão，*Rigorous absolute bounds for pion-pion scattering. II. Solving modified Szegö-Meiman problems*，Annales de l'I.H.P. A 22 (1975)，317–366，[原期刊全文](https://www.numdam.org/item/AIHPA_1975__22_4_317_0.pdf)，Appendix A：A.1 列出 Hardy 径向边界定理；A.5 给出 Hardy 边界的 Cauchy/Poisson 表示；A.6 给出实部数据的 Schwarz 表示。该附录明确将标准理论指向 Duren，*Theory of Hᵖ Spaces* (1970)。本次没有取得 Duren 原书全文，因此不伪称逐页核对过原书；上述原始研究论文附录和作者教材是本次实际核对的文本。

`schwarzIntegral ell z` **定义为实际积分**

\[
H_\ell(z)=\int_{\mathbb R/\mathbb Z}
\frac{e(t)+z}{e(t)-z}\,\ell(t)\,dt.
\]

第一个外部陈述对任意实值 `ell ∈ L∞` 和任意实常数 `L,U`，在 `L ≤ ell ≤ U` 几乎处处成立时断言：`H_ell` 在单位圆盘全纯，其实部介于 `L,U`，且 `Re H_ell(r e(t)) → ell(t)` 几乎处处。它不是声称共轭 Poisson 积分有界；有界的只是实部。

第二个外部陈述对任意单位圆盘全纯函数 `f` 及任意界 `C`，从圆盘内 `‖f‖ ≤ C` 得到 `L∞` 径向边界 `g`：几乎处处径向收敛、`‖g‖ ≤ C`、所有负 Fourier 系数为零，以及 `g` 的零 Fourier 系数等于 `f(0)`。后两项是标准 Cauchy 边界系数识别，故本条是 Fatou 与该识别的合并陈述，而不是仅把 Fourier 结论无条件附加到点态边界存在性上。

`OuterDamping.lean` 内部证明 `H_ell(0)=∫ell`，显式取 `f=exp(H_ell)`，利用实部上界证明 `‖f‖≤1`，并将边界取复共轭。由径向极限唯一性得精确模长 `exp(ell)`；再在 Lean 中代入 `ell=log(1-a u)`，证明其可测性、有界性、`exp(ell)=1-a u`、正实均值和非正 Fourier 支持。外部公理中没有参数 `a,u`，也没有假定待构造的 damping 乘子存在。

有限乘积的均值乘法性和非正 Fourier 支持保持性完全使用 Fourier Hilbert 基与 Parseval 证明；不依赖新增 Hardy 外部公理。

## 4. 没有被额外公理化的内容

- Fourier 正交性、二阶矩、四阶矩与能量的等式、基本范数界、仿射不变性及对称差扰动界，都有本项目中的 Lean 证明。
- Haar 测度、积分、有限集合、Freiman 同构等已有 mathlib 结果作为已证明的库定理使用；它们不是这里新增的外部公理。项目中的 Cauchy–Schwarz 步骤也给出了证明。
- 参考文献没有被整体变成公理。新增 Duren 相关输入仅为上面逐项陈述的两个标准通用定理；手稿自行证明的 outer damping 构造、Landau 命题等不能作为“外部引用”跳过其内部证明。
- `Statements.lean` 中的主结论规格本身只是 `Prop` 定义。编译规格不等于证明命题；具体已完成定理须以最终证明覆盖表和依赖审计为准，完整的内部证明状态见证明覆盖表。
- Lemma 6.1 的多数函数展开、平衡相位提取、有限子集双重计数、互异有序元组密度和指数常数，以及稠密块标签的遗传能量结论，均为内部证明，没有增加数学公理。相位部分使用足够的上界 `‖H‖₁ ≤ 2‖F‖₁` 和 Walsh 系数质量 `≤ 2^m`，配合子集双重计数得到手稿同一结论；不将手稿中的较尖锐中间界当作假设。

正常的 Lean 基础依赖（例如 `propext`、`Classical.choice`、`Quot.sound`）与按许可新增的数学公理应在依赖报告中分别看待。后续新增外部输入必须逐项核对其原始假设、结论和来源，不能用未完成的内部步骤填充此清单。

## 5. Green–Sanders 与背景比较

**Green–Sanders：**[发表于 Annals 的原始全文](https://annals.math.princeton.edu/wp-content/uploads/annals-v168-n3-p09.pdf)，Theorem 1.3，页 1027，归一化在页 1027–1028。`BackgroundExternal.green_sanders` 对任意有限阿贝尔群和整数值函数，使用群上归一化、对偶群上未归一化的实际 Fourier 代数范数。界为 `exp(exp(C*M^4))`，符号为 `±1`，并保留不同子群数 `≤ M+1/100` 的原结论。`GreenSandersCyclic.lean` 内部证明此范数对集合指标等于本文的 `cyclicLittlewoodNorm`；循环子群的标准余数表示及其整数等差数列提升也内部证明。这个外部定理用于额外表示备注，不用于两个主定理。

**Bloom–Green：**[作者的 arXiv:2602.16482v2 全文](https://arxiv.org/html/2602.16482v2)。`BackgroundExternal.bloom_green_inverse` 对应 Theorem 1.2 及其后关于初始段的说明；`bloom_green_constant` 对应第 4 节的参数表达式，以任意正误差和足够大基数写出渐近下界。没有将报道的 `0.170934...` 截断为一个“精确最优常数”。两条仅记录原稿的外部比较结果，本项目内部证明不依赖它们。

附录 B 的系数卷积、谱类界、零点排除、Wallis 渐近、边界幂级数、尾项估计及实际双侧完成的统一误差全部内部证明。标准 Dirichlet 核渐近也由 `IntervalAsymptotic.lean` 从已证明的块边界渐近推出，没有新增此项公理。`verification/AppendixBAudit.lean` 区分已有通用 Hardy 边界输入和纯基础依赖。完整的引文角色清单见 `BIBLIOGRAPHY_AUDIT.md`。

