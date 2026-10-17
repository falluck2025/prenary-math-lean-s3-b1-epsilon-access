import Mathlib

/-! ================================================================
   偏元数学 · Day29-03 · 界的相位 θ₀ · 位置标架的"位"
   ------------------------------------------------------------------
   对应件：NEW(S)-007 V0.5《界的升域 三层 ε 手段轴与自嵌套》（数学侧 §2、§4）。
   承：Day29-01（界的升域下的偏元累积）—— 本件接其"未做"的「界的相位 θ₀」。
   核心：界的"位"（相位）在机器上分两级：
       一级 · 相位因子：jieDir θ₀ ＝ e 的 i θ₀ 次方；相位零即单位元 1。
       二级 · 阴阳两半：由 Re 的符号定；差 π（z 映到 −z）互换两半（承 ℤ/2）。
   本稿范围：定义 2 ＋ 定理 7
       定义 jieDir（相位因子）、Yang 与 Yin（阴阳半平面）
       定理1 jieDir_zero         : 相位零 ＝ 单位元 1
       定理2 jieDir_add          : 相位可加
       定理3 jieDir_neg_mul      : 相位互逆（与 −θ 相乘为 1）
       定理4 yang_or_yin_or_axis : 任一点：阳、阴、或在轴上（三分）
       定理5 not_yang_and_yin    : 阴阳互斥
       定理6 yang_neg_iff_yin    : 差 π（z 映到 −z）互换阴阳
       定理7 axis_neg            : 主轴（Re ＝ 0）在差 π 下不变
   不做：不做 θ₀ 与 ⟨e 的 iφ 次方⟩ 的等号（S-007 §6 待达 2，P1 候选，未证）；
        不引入任何经验常数；不写复数辐角 arg（留待后续件）。
   注：本件抬头内不出现「斜杠紧跟连字符」的写法，避免嵌套注释。
   日期：2026-10-07
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryS007
noncomputable section

/-- 界的相位因子：jieDir θ₀ ＝ e 的 i θ₀ 次方。（位置标架的"位"） -/
noncomputable def jieDir (θ₀ : ℝ) : ℂ := Complex.exp (Complex.I * (θ₀ : ℂ))

/-- 阳半平面（过冲面）：Re 为正。 -/
def Yang (z : ℂ) : Prop := 0 < z.re

/-- 阴半平面（不足面）：Re 为负。 -/
def Yin (z : ℂ) : Prop := z.re < 0

-- 定理1：相位零 ＝ 单位元（乘性退化）
theorem jieDir_zero : jieDir 0 = 1 := by
  simp [jieDir]

-- 定理2：相位可加
theorem jieDir_add (a b : ℝ) : jieDir (a + b) = jieDir a * jieDir b := by
  simp only [jieDir]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

-- 定理3：相位互逆：jieDir(−θ) 乘 jieDir θ ＝ 1
theorem jieDir_neg_mul (θ₀ : ℝ) : jieDir (-θ₀) * jieDir θ₀ = 1 := by
  simp only [jieDir]
  rw [← Complex.exp_add]
  have h : Complex.I * ↑(-θ₀) + Complex.I * ↑θ₀ = 0 := by
    push_cast
    ring
  rw [h, Complex.exp_zero]

-- 定理4：阴阳三分轴（任一点：阳、阴、或在轴上）
theorem yang_or_yin_or_axis (z : ℂ) : Yang z ∨ Yin z ∨ z.re = 0 := by
  rcases lt_trichotomy z.re 0 with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inl h

-- 定理5：阴阳互斥（不能既是阳又是阴）
theorem not_yang_and_yin (z : ℂ) : ¬ (Yang z ∧ Yin z) := by
  intro h
  exact (not_lt_of_gt h.1) h.2

-- 定理6：差 π（z 映到 −z）互换阴阳
theorem yang_neg_iff_yin (z : ℂ) : Yang (-z) ↔ Yin z := by
  simp only [Yang, Yin, Complex.neg_re]
  exact neg_pos

-- 定理7：主轴（Re ＝ 0）在差 π 下不变
theorem axis_neg (z : ℂ) (h : z.re = 0) : (-z).re = 0 := by
  rw [Complex.neg_re, h, neg_zero]

end
end PrenaryS007
