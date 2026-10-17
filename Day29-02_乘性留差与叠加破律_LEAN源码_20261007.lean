import Mathlib

/-! ================================================================
   偏元数学 · Day29-02 · 偏元运算的代数结构（乘性侧）与"叠加破律"
   ------------------------------------------------------------------
   缘起（2026-10-07）：焊 08-30《偏元留差谱》两死穴的"底层公理版"。
       问题：乘性留差与加性残差"叠加"时，是否破坏群律（结合律、单位元）？
       本件答案：
         · 加性 ⊕（a + b + ε）：结合律保持、单位元为 −ε（承 Day13）。
         · 加性残差叠到乘法（a·b + ε）：结合律破，破律量 = ε·(c − a)，正比于 ε。
         · 相位型乘性留差（a·b·e^{iε}）：结合律保持、单位元为 e^{−iε}，不破律。
         · 叠加（相位 + 加性残差）：破律量 = ε₂·e^{iε₁}·(c − a)，仍正比于加性残差。
       ⟹ 破律的承重者是"加性残差"，不是"相位型乘性留差"。
   宗旨：本件只立定义与它们相对经典多出来的那点东西；不替 ε 取值。
   层位：本件挂在动作层 L1 上；与投影 π 由 L1 到 L0 的关系见抬头上段。
   承：Day13 偏元加法；Day26-01 偏元减法（ε 取复数）。
   注：本件抬头内不出现"斜杠紧跟连字符"的写法，避免嵌套注释。
   日期：2026-10-07
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryS006

/-- 偏元加法：a ⊕ b = a + b + ε。（承 Day13） -/
def oplus (ε a b : ℂ) : ℂ := a + b + ε

/-- 加性残差叠到乘法：a ⊗ b = a·b + ε。 -/
def omulAdd (ε a b : ℂ) : ℂ := a * b + ε

/-- 相位型乘性留差：a ⊗ b = a·b·e^{iε}。 -/
noncomputable def omulPhase (ε a b : ℂ) : ℂ := a * b * Complex.exp (Complex.I * ε)

/-- 叠加：相位型乘性留差 + 加性残差：a ⊗ b = a·b·e^{iε₁} + ε₂。 -/
noncomputable def ostk (ε₁ ε₂ a b : ℂ) : ℂ := a * b * Complex.exp (Complex.I * ε₁) + ε₂

-- 定理 1：加性 ⊕ 结合律保持（承 Day13）
theorem oplusAssoc (ε a b c : ℂ) :
    oplus ε (oplus ε a b) c = oplus ε a (oplus ε b c) := by
  simp only [oplus]
  ring

-- 定理 2：加性 ⊕ 的单位元为 −ε（承 Day13）
theorem oplusUnit (ε a : ℂ) : oplus ε a (-ε) = a := by
  simp only [oplus]
  ring

-- 定理 3：omulAdd 破律量 = ε·(c − a)
theorem omulAddAssocGap (ε a b c : ℂ) :
    omulAdd ε (omulAdd ε a b) c - omulAdd ε a (omulAdd ε b c) = ε * (c - a) := by
  simp only [omulAdd]
  ring

-- 定理 4：ε ≠ 0 且 c ≠ a 时，omulAdd 破坏结合律
theorem omulAddBreaksAssoc (ε a c : ℂ) (hε : ε ≠ 0) (hca : c ≠ a) (b : ℂ) :
    omulAdd ε (omulAdd ε a b) c ≠ omulAdd ε a (omulAdd ε b c) := by
  intro h
  have hg := omulAddAssocGap ε a b c
  rw [h, sub_self] at hg
  exact (mul_ne_zero hε (sub_ne_zero.mpr hca)) hg.symm

-- 定理 5：相位型 omulPhase 结合律保持
theorem omulPhaseAssoc (ε a b c : ℂ) :
    omulPhase ε (omulPhase ε a b) c = omulPhase ε a (omulPhase ε b c) := by
  simp only [omulPhase]
  ring

-- 定理 6：相位型 omulPhase 的单位元为 e^{−iε}
theorem omulPhaseUnit (ε a : ℂ) :
    omulPhase ε a (Complex.exp (-(Complex.I * ε))) = a := by
  simp only [omulPhase]
  have h : Complex.exp (Complex.I * ε) * Complex.exp (-(Complex.I * ε)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  calc a * Complex.exp (-(Complex.I * ε)) * Complex.exp (Complex.I * ε)
      = a * (Complex.exp (Complex.I * ε) * Complex.exp (-(Complex.I * ε))) := by ring
    _ = a * 1 := by rw [h]
    _ = a := by ring

-- 定理 7：叠加 ostk 的破律量 = ε₂·e^{iε₁}·(c − a)
theorem ostkAssocGap (ε₁ ε₂ a b c : ℂ) :
    ostk ε₁ ε₂ (ostk ε₁ ε₂ a b) c - ostk ε₁ ε₂ a (ostk ε₁ ε₂ b c)
      = ε₂ * Complex.exp (Complex.I * ε₁) * (c - a) := by
  simp only [ostk]
  ring

-- 定理 8：叠加的破律只来自加性残差；ε₂ = 0（只剩相位型）时不破律
theorem ostkPhaseOnly (ε₁ a b c : ℂ) :
    ostk ε₁ 0 (ostk ε₁ 0 a b) c = ostk ε₁ 0 a (ostk ε₁ 0 b c) := by
  simp only [ostk]
  ring

-- 定理 9：退化（关 4）—— ε = 0 时，加性 ⊕ 回到经典加法
theorem oplusDegenerate (a b : ℂ) : oplus 0 a b = a + b := by
  simp only [oplus, add_zero]

-- 定理 10：退化（关 4）—— ε = 0 时，omulAdd 回到经典乘法
theorem omulAddDegenerate (a b : ℂ) : omulAdd 0 a b = a * b := by
  simp only [omulAdd, add_zero]

-- 定理 11：退化（关 4）—— ε = 0 时，相位型回到经典乘法
theorem omulPhaseDegenerate (a b : ℂ) : omulPhase 0 a b = a * b := by
  simp only [omulPhase, mul_zero, Complex.exp_zero, mul_one]

end PrenaryS006
