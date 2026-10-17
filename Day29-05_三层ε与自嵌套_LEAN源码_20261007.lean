import Mathlib

/-! ================================================================
   偏元数学 · Day29-05 · 三层 ε 与自嵌套（可机器化的部分）
   ------------------------------------------------------------------
   对应件：NEW(S)-007 V0.5 §14（三层 ε）与 §15（自嵌套）。
   核心：以「投影」刻画三层的机器骨架 ——
       母体 v 经投影 π 得 classic ＝ π v；剔除 classic 后的剩余 still ＝ v 减 π v；
       两式并出：v ＝ classic 加 still（分解），且 π 为幂等投影。
       层链：layer π v n 为反复作用 π；幂等投影下层链自第一层起恒定。
   本稿范围：定义 4 ＋ 定理 6
       定义 isProjection（幂等）、classic、still、layer
       定理1 decomp             : classic 加 still ＝ 母体（两式并出的机器版）
       定理2 pi_classic         : π 作用在 classic 上不动（幂等）
       定理3 pi_still_zero      : π 作用在 still 上为 0（still 不被经典收走）
       定理4 still_classic_zero : classic 自身的 still 为 0
       定理5 layer_succ         : 层链递推
       定理6 layer_grows        : 幂等投影下，层链自第一层起恒定
   不做：不做「自嵌套层无底（无限层）」的机器化 —— 幂等投影模型下层链恒定，
        真「层无底」需更一般的再嵌入结构，本件只在陈述层保留该命题。
        不替 ε 取值；不做接口 B（跨侧 ε 与 η）的机器化。
   注：本件不用求和记法；抬头内不出现「斜杠紧跟连字符」的写法。
   日期：2026-10-07
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryS007
noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- 投影（幂等线性映射）：把母体投到"经典能认领"的那一部分。 -/
def isProjection (π : E →ₗ[ℝ] E) : Prop := ∀ v : E, π (π v) = π v

/-- 第一层 · classic：投影像。 -/
def classic (π : E →ₗ[ℝ] E) (v : E) : E := π v

/-- 第三层 · still：母体剔除 classic 后的剩余。 -/
def still (π : E →ₗ[ℝ] E) (v : E) : E := v - π v

/-- 层链：反复作用 π。 -/
def layer (π : E →ₗ[ℝ] E) (v : E) : ℕ → E :=
  fun n => Nat.rec v (fun _ acc => π acc) n

-- 定理1：母体 ＝ classic 加 still（两式并出的机器版）
theorem decomp (π : E →ₗ[ℝ] E) (v : E) : classic π v + still π v = v := by
  change π v + (v - π v) = v
  abel

-- 定理2：π 作用在 classic 上不动（幂等）
theorem pi_classic (π : E →ₗ[ℝ] E) (hπ : isProjection π) (v : E) :
    π (classic π v) = classic π v := by
  change π (π v) = π v
  exact hπ v

-- 定理3：π 作用在 still 上为 0（still 不被经典收走）
theorem pi_still_zero (π : E →ₗ[ℝ] E) (hπ : isProjection π) (v : E) :
    π (still π v) = 0 := by
  change π (v - π v) = 0
  rw [map_sub, hπ v, sub_self]

-- 定理4：classic 自身的 still 为 0
theorem still_classic_zero (π : E →ₗ[ℝ] E) (hπ : isProjection π) (v : E) :
    still π (classic π v) = 0 := by
  change classic π v - π (classic π v) = 0
  rw [pi_classic π hπ v, sub_self]

-- 定理5：层链递推
theorem layer_succ (π : E →ₗ[ℝ] E) (v : E) (n : ℕ) :
    layer π v (n + 1) = π (layer π v n) := by
  simp [layer]

-- 定理6：幂等投影下，层链自第一层起恒定
theorem layer_grows (π : E →ₗ[ℝ] E) (hπ : isProjection π) (v : E) (n : ℕ) :
    layer π v (n + 1) = classic π v := by
  induction n with
  | zero => simp [layer, classic]
  | succ k ih =>
    rw [layer_succ, ih]
    change π (π v) = π v
    exact hπ v

end
end PrenaryS007
