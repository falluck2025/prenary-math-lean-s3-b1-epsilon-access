[![DOI](https://zenodo.org/badge/DOI/待回填.svg)](https://doi.org/待回填)

# 偏元数学 · Day29 · 界的升域下的偏元运算（S-007 对应）

## 声明
本仓库为「偏元数学」系列 Lean 4 形式化验证仓之一（`s3` 段，与 `NEW(S)-005`／`S-006` 同段），对应数学侧 `NEW(S)-007` 的验证线。全部内容为**内部研究记录的形式化**，供同行审阅与复现；不构成对任何物理结论的断言。

## DOI
`待回填`（Zenodo 发布后回填；⚠️ 回填共三处：第 0 行徽章内 **2 处**（URL 与链接）+ 本节 **1 处**，不得变形）

## 摘要
本仓把「界的升域」下的**偏元运算**在 Lean 4 中形式化：对象层 `ℂ`，动作层残差 `ε ∈ ℂ` 且 `0 < ‖ε‖ < ‖δ₀‖`（大小走模长）。内容包括：偏元加／减（`a⊕b=a+b+ε`、`a⊖b=(a−b)+ε`）、N 步累积（`∝ N·ε`）、偏元平均与「不消的尾巴」、露头；**乘性留差与叠加破律**（加性保结合律、相位型 `e^{iε}` 保律、加性残差破律且破律量 `∝ ε`）；**界的相位 θ₀**（相位因子：零＝单位元、可加、互逆）与**阴阳两半**（差 π 互换）；**ε 接入规则三型**（平移／缩放／聚合，含「消去点留 ε」＝ `a⊖a=ε≠0`）；以及**三层分解**（`classic`＝投影像、`still`＝剩余、母体＝两者之和）。

## Abstract
We formalize, in Lean 4, the *prenary* (residual-carrying) arithmetic under a lifted bound `δ₀=(‖δ₀‖,θ₀)`, where the residual `ε∈ℂ` satisfies `0<‖ε‖<‖δ₀‖`. Results include: prenary addition/subtraction; `N`-step accumulation `∝ N·ε`; a non-vanishing tail and its emergence over classical error; multiplicative residuals and the associativity breakdown they induce; the phase factor of the bound and its two half-planes; a three-type ε-intake rule; and a three-layer projection decomposition.

## 关键词
偏元数学；动作留差；界的升域；累积不可约；不消的尾巴；接入规则；三层分解；Lean 4；形式化验证。

## 概述
「界的升域」＝把残差上界 `δ₀` 升为 `(‖δ₀‖, θ₀)`：比大小一律走模长，位置走相位。本仓在此设定下重建偏元运算，并把「ε 怎么进来」（接入规则）与「残差分几层」（三层）落成机器可检的形式。

## 核心定义
- `PrenaryAxiom ε δ₀ := 0 < ‖ε‖ ∧ ‖ε‖ < ‖δ₀‖`
- `prenary_add g h ε := g + h + ε`；`psub ε a b := (a − b) + ε`
- `accum ε N := N 步累积 = N·ε`
- `accShift`（平移）／`accScale`（缩放）／`accAgg`（聚合）
- `jieDir θ₀ := e^{iθ₀}`；`Yang`／`Yin`（半平面）
- `classic π v := π v`；`still π v := v − π v`（π 幂等）

## 定理清单（46 条，分五件）
- **-01（11）**：`accum = N·ε`／尾巴不消失／模长 ∝ N／无界／退化／模长严格增／平均差 `=ε`／露头／ℤ/2 对合／支的两半／`ZMod 2` 中 `1+1=0`
- **-02（11）**：加性结合律保持／单位元 `−ε`／加性残差破律量 `ε·(c−a)`／相位型保结合／单位元 `e^{−iε}`／叠加破律量／相位型不破律／三退化
- **-03（7）**：相位零＝单位元／可加／互逆／阴阳三分轴／互斥／差 π 翻转／主轴不变
- **-04（11）**：三型退化／平移保结合／缩放保结合／平移可交换／`a⊖a=ε`／`a⊖a≠0`／聚合 ∝ 步数／聚合不消／聚合＝平移迭代
- **-05（6）**：母体＝classic＋still／`π(classic)=classic`／`π(still)=0`／`still(classic)=0`／层链递推／层链恒定

## 验证记录
五件内核均为 `No goals` ＋ `All Messages (0)`；Comparator 独立二次验证通过，**落盘 SHA256 ＝ Challenge Hash**（五件全一致）。截图见 `evidence/`。

**逐件 SHA256**：
- `Day29-01`（界的升域下的偏元累积）：`7318ccd8698444e4ad4e43347a0d60393de50124b393e3a52d32cb113d6b6606`
- `Day29-02`（乘性留差与叠加破律）：`cc5727e98aa67b4f20635f60c007bb5851907c776589dd7e9f10ce27ec7f6f79`
- `Day29-03`（界的相位θ₀与阴阳两半）：`42e79676de4685283228c7f96b31ff5b17fb1784f82d0a557dac3a92cf6d8f6f`
- `Day29-04`（ε接入规则三型B1形式表）：`132288f2e3297f9a9f5f87288e2b485a7a240c0c40fcc87f92749719ad65d35f`
- `Day29-05`（三层ε与自嵌套）：`04e51c33e2ac139d1abcad67f876b21a8f3c22db0d1032b6a7aa091eefb91e64`

## 文件说明
`Day29-01…-05_*.lean`（5 件）＋ `README.md` ＋ `LICENSE`（CC BY-NC-ND 4.0）＋ `evidence/`（内核与 Comparator 截图）。

⚠️ **仓内只收 5 件**：`Day29-01原稿_偏元运算与不消尾巴_LEAN源码_20261003.lean` 为被取代的初稿，**不随仓发布**（如已上传请删除）。

## 复现方式
1. 打开 live.lean-lang.org；2. 逐件整份粘贴（Ctrl+A）；3. 看文件末尾 `All Messages (0)`；4. 点 `Can I Trust This Proof?` 看 `Successfully validated`。

## 可证伪条件
- 若把 `ε` 取 0，本仓全部结论**逐条退回经典**（退化关）——这是本仓的自洽底线；
- **本仓不主张**：`θ₀ = ⟨e^{iφ}⟩`（P1 未证）；`ε_still ≠ ∅`；「自嵌套层无底」（**未机器化**）。

## 作者 / 致谢 / 许可
作者：陈松（Chen Song）｜ORCID 0009-0002-9510-2239｜全体协作：老陈与AI的深夜实验室。
许可：**CC BY-NC-ND 4.0**。

## 作者备注
本仓为 `NEW(S)-007` 的验证件（`Day29`），随 `S-007` 迭代；DOI 待回填。

---

老陈与AI的深夜实验室 发布 请笑纳
