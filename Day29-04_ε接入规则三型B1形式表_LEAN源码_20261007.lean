import Mathlib

/-! ================================================================
   偏元数学 · Day29-04 · ε 的接入规则三型（B1 形式表）
   ------------------------------------------------------------------
   对应件：NEW(S)-007 V0.5 §19（B1 接入规则）＋ 基准范式 关 2（残差用 ⊖）。
   承：Day29-01（界的升域下的偏元累积）—— 本件把"ε 怎么进来"列成三型。
   核心：接入形式由运算的代数类型定：
       ① 平移型（加与减）：a ⊕ b ＝ a 加 b 加 ε
       ② 缩放型（乘与归一）：a ⊗ b ＝ a 乘 b 乘（1 加 η）
       ③ 聚合型（和与平均与累积）：accAgg ε N ＝ N 乘 ε
   本稿范围：定义 4 ＋ 定理 11
       定义 accShift、accScale、accAgg、psub
       定理1  accShift_degenerate : ε 取 0 时回经典加
       定理2  accScale_degenerate : η 取 0 时回经典乘
       定理3  accAgg_zero         : 0 步聚合为 0
       定理4  accShift_assoc      : 平移型保结合律
       定理5  accScale_assoc      : 缩放型保结合律
       定理6  accShift_comm       : 平移型可交换
       定理7  psub_self           : a ⊖ a ＝ ε（消去点留 ε）
       定理8  psub_self_ne_zero   : ε ≠ 0 时 a ⊖ a ≠ 0（减法不清零）
       定理9  accAgg_norm         : 聚合型模长 ＝ N 乘 ‖ε‖（正比于步数）
       定理10 accAgg_ne_zero      : 聚合型不消
       定理11 accAgg_succ         : 聚合 ＝ 平移迭代（三型关系）
   不做：不替 ε 与 η 取值；不做 θ₀ 的机器化（已属 Day29-03）。
   注：本件不用求和记法；抬头内不出现「斜杠紧跟连字符」的写法。
   日期：2026-10-07
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryS007
noncomputable section

/-- 接入规则 · 平移型：a ⊕ b ＝ a 加 b 加 ε。（加／减用） -/
noncomputable def accShift (ε a b : ℂ) : ℂ := a + b + ε

/-- 接入规则 · 缩放型：a ⊗ b ＝ a 乘 b 乘（1 加 η）。（乘／归一用） -/
noncomputable def accScale (η a b : ℂ) : ℂ := a * b * (1 + η)

/-- 接入规则 · 聚合型：N 步累积 ＝ N 乘 ε。（和／平均／累积用） -/
noncomputable def accAgg (ε : ℂ) (N : ℕ) : ℂ := (N : ℂ) * ε

/-- 偏元减（承 Day29-01）：a ⊖ b ＝（a 减 b）加 ε。（消去点留 ε） -/
noncomputable def psub (ε a b : ℂ) : ℂ := (a - b) + ε

-- 定理1：平移型退化（ε 取 0 回经典加）
theorem accShift_degenerate (a b : ℂ) : accShift 0 a b = a + b := by
  simp [accShift]

-- 定理2：缩放型退化（η 取 0 回经典乘）
theorem accScale_degenerate (a b : ℂ) : accScale 0 a b = a * b := by
  simp [accScale]

-- 定理3：聚合型 0 步为 0
theorem accAgg_zero (ε : ℂ) : accAgg ε 0 = 0 := by
  simp [accAgg]

-- 定理4：平移型保结合律
theorem accShift_assoc (ε a b c : ℂ) :
    accShift ε (accShift ε a b) c = accShift ε a (accShift ε b c) := by
  simp only [accShift]
  ring

-- 定理5：缩放型保结合律
theorem accScale_assoc (η a b c : ℂ) :
    accScale η (accScale η a b) c = accScale η a (accScale η b c) := by
  simp only [accScale]
  ring

-- 定理6：平移型可交换
theorem accShift_comm (ε a b : ℂ) : accShift ε a b = accShift ε b a := by
  simp only [accShift]
  ring

-- 定理7：消去点留 ε：a ⊖ a ＝ ε
theorem psub_self (ε a : ℂ) : psub ε a a = ε := by
  simp [psub]

-- 定理8：减法不清零：ε ≠ 0 时 a ⊖ a ≠ 0
theorem psub_self_ne_zero (ε a : ℂ) (hε : ε ≠ 0) : psub ε a a ≠ 0 := by
  rw [psub_self]
  exact hε

-- 预备：ℕ 在 ℂ 中的模长（承 Day29-01 同法复刻）
theorem norm_natCast_complex (n : ℕ) : ‖((n : ℕ) : ℂ)‖ = (n : ℝ) := by
  have h : ‖((n : ℕ) : ℂ)‖ ^ 2 = (n : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_natCast]
    ring
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [h, norm_nonneg ((n : ℕ) : ℂ), hn0]

-- 定理9：聚合型模长 ＝ N 乘 ‖ε‖（正比于步数）
theorem accAgg_norm (ε : ℂ) (N : ℕ) : ‖accAgg ε N‖ = (N : ℝ) * ‖ε‖ := by
  rw [accAgg, norm_mul, norm_natCast_complex]

-- 定理10：聚合型不消
theorem accAgg_ne_zero (ε : ℂ) (hε : ε ≠ 0) {N : ℕ} (hN : N ≠ 0) :
    accAgg ε N ≠ 0 := by
  rw [accAgg]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hN) hε

-- 定理11：聚合 ＝ 平移迭代（三型关系）
theorem accAgg_succ (ε : ℂ) (N : ℕ) :
    accAgg ε (N + 1) = accShift ε (accAgg ε N) 0 := by
  simp only [accAgg, accShift, Nat.cast_succ]
  ring

end
end PrenaryS007
