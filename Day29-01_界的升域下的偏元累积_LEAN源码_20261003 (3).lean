import Mathlib

/-! ================================================================
   偏元数学 · Day29-01 · S-007 起跑线 · 界的升域下的偏元累积
   ------------------------------------------------------------------
   对应件：NEW(S)-007 V0.1《界的升域与位置标架的两级结构》（数学侧）。
           Day29 起于 NEW(S)-007 的 V0.1；本件随 S-007 的迭代进度推进。
   承接（同名同形式复刻 —— 单文件不共享，必须自带）：
     ① 偏元加法 prenary_add g h ε = g + h + ε   ← 承 Day13（偏元代数 · 单位元偏移）
     ② 偏元减法 psub ε a b = (a - b) + ε        ← 承 Day26-01（S3 · 方向回归 · 代数与序）
   本件在其上加「累积」这一层：N 步偏元累积、偏元平均、以及不消的尾巴。
   层位：动作层 L1（不是对象层 L0）。
   ⭐ 界的升域（S-007 §2）：δ₀ := (‖δ₀‖, θ₀)；大小一律走模长，位走相位。
      故本件中凡「比大小」者，一律写模长版（ℂ 无全序）。
   本稿范围：三条公理层 ＋ 一条预备 ＋ 两条递推 ＋ 十一条定理
     公理  PrenaryAxiom        : 0 < ‖ε‖ ∧ ‖ε‖ < ‖δ₀‖        （S-007 设定 1′）
     预备  norm_natCast_complex: ‖↑n‖ = n                    （模长：ℕ 在 ℂ 中）
     递推  prenary_accum_zero / prenary_accum_succ : 0 步为 0，每步加 ε
     定理1 prenary_accum_eq              : N 步累积 = N · ε           （正比于步数）
     定理2 prenary_accum_ne_zero         : ε ≠ 0 ⟹ 非零步后累积 ≠ 0
     定理3 prenary_accum_norm            : ‖累积 N 步‖ = N · ‖ε‖
     定理4 prenary_accum_unbounded       : ε ≠ 0 ⟹ 模长无界（资源加倍也抹不掉）
     定理5 prenary_accum_degenerate      : ε = 0 ⟹ 累积 ≡ 0           （关掉 ε 回到经典）
     定理6 prenary_accum_norm_strictMono : ε ≠ 0 ⟹ 模长随步数严格递增
     定理7 prenary_avg_gap               : 偏元平均 − 经典平均 = ε（与样本量无关）
     定理8 prenary_tail_emerges          : 经典误差 c 除以（N 加 1）终会小于 ‖ε‖
     定理9 prenary_neg_involution        : 差 π（z 映到 −z）是阶 2 的对合
     定理10 prenary_neg_ne_self          : z ≠ 0 ⟹ −z ≠ z            （支的两半）
     定理11 prenary_two_state_add_self   : ℤ/2 中 1 + 1 = 0（二态＝阶 2，承 Day26-04）
   不做：不做「界的相位 θ₀」的机器化（属下一件）；不引入任何经验常数。
   注：本件不用求和记法，直接写 Finset.sum。
   注：抬头内不出现「斜杠紧跟连字符」的写法，避免嵌套注释。
   日期：2026-10-03
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryS007

noncomputable section

-- ============================ 公理层（S-007 设定 1′） ============================

/-- 公理层：残差与界的模长关系（大小走模长）。
    ⚠️ 设定 2′（‖δ₀‖ 不可达）在本件为陈述，未机器化。 -/
def PrenaryAxiom (ε δ₀ : ℂ) : Prop := 0 < ‖ε‖ ∧ ‖ε‖ < ‖δ₀‖

/-- 由公理层得：ε 非零。 -/
theorem prenary_axiom_ne_zero {ε δ₀ : ℂ} (h : PrenaryAxiom ε δ₀) : ε ≠ 0 :=
  norm_pos_iff.mp h.1

/-- 由公理层得：模长有上界。 -/
theorem prenary_axiom_bound {ε δ₀ : ℂ} (h : PrenaryAxiom ε δ₀) : ‖ε‖ < ‖δ₀‖ := h.2

-- ============================ 承接定义（复刻） ============================

/-- 偏元加法：g ⊕ h = g + h + ε。（承 Day13 `prenary_add`，此处复刻。） -/
noncomputable def prenary_add (g h ε : ℂ) : ℂ := g + h + ε

/-- 偏元减法：a ⊖ b = (a 减 b) 加 ε。（承 Day26-01 `psub`，此处复刻。）（**关2 残差关**） -/
noncomputable def psub (ε a b : ℂ) : ℂ := (a - b) + ε

/-- N 步偏元累积：从 0 出发，每一步把「加一个 0」喂给偏元加法。
    ⚠️ 用 `Nat.rec` 而不用模式匹配 —— 模式匹配会生成私有辅助常量
    （`_private.….accum.match_1`），会让 Comparator 的导出器 PANIC。 -/
noncomputable def accum (ε : ℂ) : ℕ → ℂ :=
  fun N => Nat.rec 0 (fun _ acc => prenary_add acc 0 ε) N

/-- 递推式（0 步）：累积 0 步为 0。 -/
theorem prenary_accum_zero (ε : ℂ) : accum ε 0 = 0 := by simp [accum]

/-- 递推式（后继步）：每一步加 ε。 -/
theorem prenary_accum_succ (ε : ℂ) (n : ℕ) :
    accum ε (n + 1) = prenary_add (accum ε n) 0 ε := by simp [accum]

-- ============================ 预备 ============================

/-- 预备（模长）：ℕ 在 ℂ 中的模长等于它自己。
    ⚠️ 若 `Complex.normSq_eq_norm_sq` 名称对不上，可改用 `Complex.sq_norm` 重写这一条。 -/
theorem norm_natCast_complex (n : ℕ) : ‖((n : ℕ) : ℂ)‖ = (n : ℝ) := by
  have h : ‖((n : ℕ) : ℂ)‖ ^ 2 = (n : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_natCast]
    ring
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [h, norm_nonneg ((n : ℕ) : ℂ), hn0]

-- ============================ 定理 ============================

/-- 定理1（正比于步数）：N 步偏元累积 = N 乘 ε。 -/
theorem prenary_accum_eq (ε : ℂ) (N : ℕ) : accum ε N = (N : ℂ) * ε := by
  induction N with
  | zero => simp [prenary_accum_zero]
  | succ n ih => simp only [prenary_accum_succ, ih, prenary_add, Nat.cast_succ]; ring

/-- 定理2（尾巴不消失）：ε 非零，则任意非零步数之后，累积仍非零。 -/
theorem prenary_accum_ne_zero (ε : ℂ) (hε : ε ≠ 0) {N : ℕ} (hN : N ≠ 0) :
    accum ε N ≠ 0 := by
  rw [prenary_accum_eq]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hN) hε

/-- 定理3（模长关系）：累积 N 步的模长 = N 乘 ‖ε‖。 -/
theorem prenary_accum_norm (ε : ℂ) (N : ℕ) : ‖accum ε N‖ = (N : ℝ) * ‖ε‖ := by
  rw [prenary_accum_eq, norm_mul, norm_natCast_complex]

/-- 定理4（模长无界）：ε 非零，则无论给多大的界限 M，都能用足够多的步数越过它。
    ⟹ 这是「资源加倍也抹不掉」的机器侧说法。 -/
theorem prenary_accum_unbounded (ε : ℂ) (hε : ε ≠ 0) (M : ℝ) :
    ∃ N : ℕ, M < ‖accum ε N‖ := by
  have hc : 0 < ‖ε‖ := norm_pos_iff.mpr hε
  obtain ⟨n, hn⟩ := exists_nat_gt (M / ‖ε‖)
  refine ⟨n + 1, ?_⟩
  rw [prenary_accum_norm, Nat.cast_succ]
  have h1 : M < (n : ℝ) * ‖ε‖ := by
    have h := mul_lt_mul_of_pos_right hn hc
    rwa [div_mul_cancel₀ M (ne_of_gt hc)] at h
  nlinarith [h1, hc]

/-- 定理5（退化）：关掉 ε（取 ε = 0），累积回到经典——恒为 0。（**关4 退化关**） -/
theorem prenary_accum_degenerate (N : ℕ) : accum 0 N = 0 := by
  rw [prenary_accum_eq]
  simp

/-- 定理6（模长严格递增）：ε 非零，则累积的模长随步数严格递增。 -/
theorem prenary_accum_norm_strictMono (ε : ℂ) (hε : ε ≠ 0) :
    StrictMono (fun N : ℕ => ‖accum ε N‖) := by
  have hc : 0 < ‖ε‖ := norm_pos_iff.mpr hε
  intro m n hmn
  have hm : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  show ‖accum ε m‖ < ‖accum ε n‖
  rw [prenary_accum_norm, prenary_accum_norm]
  exact mul_lt_mul_of_pos_right hm hc

-- ============================ 平均（尾巴不消 · 平均版） ============================

/-- 经典平均：把和除以样本量。 -/
noncomputable def classicAvg {ι : Type*} (s : Finset ι) (f : ι → ℂ) : ℂ :=
  (s.sum f) / (s.card : ℂ)

/-- 偏元平均：经典平均再加 ε。 -/
noncomputable def prenaryAvg {ι : Type*} (ε : ℂ) (s : Finset ι) (f : ι → ℂ) : ℂ :=
  (s.sum f) / (s.card : ℂ) + ε

/-- 定理7（不消的尾巴 · 平均版）：偏元平均与经典平均之差恒为 ε，
    **与样本量无关** —— 经典统计误差随样本量减小，这一项不减。 -/
theorem prenary_avg_gap {ι : Type*} (ε : ℂ) (s : Finset ι) (f : ι → ℂ) :
    prenaryAvg ε s f - classicAvg s f = ε := by
  simp [prenaryAvg, classicAvg]

-- ============================ 露头 ============================

/-- 定理8（露头）：经典误差取 c 除以（N 加 1）（随资源减小），偏元尾巴 ‖ε‖ 恒定；
    则资源足够时，经典误差必小于 ‖ε‖。
    ⟹ 「精度上去之后，剩下的那个，是我们」。 -/
theorem prenary_tail_emerges (c : ℝ) (ε : ℂ) (hε : ε ≠ 0) :
    ∃ N : ℕ, c / ((N : ℝ) + 1) < ‖ε‖ := by
  have hc : 0 < ‖ε‖ := norm_pos_iff.mpr hε
  obtain ⟨n, hn⟩ := exists_nat_gt (c / ‖ε‖)
  refine ⟨n, ?_⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlt : c / ‖ε‖ < (n : ℝ) + 1 := by linarith
  have h2 : c < ((n : ℝ) + 1) * ‖ε‖ := by
    have h := mul_lt_mul_of_pos_right hlt hc
    rwa [div_mul_cancel₀ c (ne_of_gt hc)] at h
  rw [div_lt_iff₀ hpos, mul_comm ‖ε‖ ((n : ℝ) + 1)]
  exact h2

-- ============================ ℤ/2：差 π 的两半 ============================

/-- 定理9（阶 2 的对合）：z 映到 −z，两次回到自身。
    ⟹ 「差 π」这一级是 ℤ/2 的作用（NEW(S)-007 V0.1 §4；承 Day26-04 二态的对合性）。 -/
theorem prenary_neg_involution (z : ℂ) : -(-z) = z := neg_neg z

/-- 定理10（支的两半）：z 非零时，−z 与 z 是两个不同的支。 -/
theorem prenary_neg_ne_self {z : ℂ} (hz : z ≠ 0) : -z ≠ z := by
  intro h
  have h2 : (2 : ℂ) * z = 0 := by
    rw [two_mul]
    have hh : z + (-z) = 0 := add_neg_cancel z
    rw [h] at hh
    exact hh
  exact hz ((mul_eq_zero.mp h2).resolve_left (by norm_num))

/-- 定理11（二态 ＝ 阶 2）：ℤ/2 中 1 + 1 = 0。（承 Day26-04） -/
theorem prenary_two_state_add_self : (1 : ZMod 2) + 1 = 0 := by decide

end

end PrenaryS007
