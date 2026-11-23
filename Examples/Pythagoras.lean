/-
勾股定理（Pythagorean theorem）的几种 Lean 4 形式。
每个定理都已在本机 Lean 4.36.0 + Mathlib 上编译通过，
`#print axioms` 显示只依赖 Lean 的三条标准公理。
-/
import Mathlib

open scoped RealInnerProductSpace

/-! ## 版本 1：抽象实内积空间中的勾股定理

设 `x, y` 是实内积空间 `V` 中的向量，若它们正交（`⟪x, y⟫ = 0`），
则 `‖x + y‖² = ‖x‖² + ‖y‖²`。
这是勾股定理的"本质形式"：两条直角边是 `x`、`y`，斜边是 `x + y`。
-/
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem pythagoras (x y : V) (h : ⟪x, y⟫ = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  -- 第一步：展开 ‖x + y‖² = ‖x‖² + 2⟪x,y⟫ + ‖y‖²
  rw [norm_add_sq_real]
  -- 第二步：用正交条件 ⟪x,y⟫ = 0 消掉交叉项
  rw [h]
  -- 第三步：剩下 ‖x‖² + 2·0 + ‖y‖² = ‖x‖² + ‖y‖²，纯算术
  ring

/-! ## 版本 2：把上面的展开"手算"一遍，看清每一步用的是哪条公理

`norm_add_sq_real` 本身就是被证明出来的引理，这里我们不调用它，
而是从内积的双线性、对称性和 `‖v‖² = ⟪v, v⟫` 出发重建同一件事。
-/
theorem pythagoras_scratch (x y : V) (h : ⟪x, y⟫ = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  -- 把三个 ‖·‖² 都换成内积 ⟪·,·⟫（用 ‖v‖² = ⟪v,v⟫ 的反向）
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq x,
      ← real_inner_self_eq_norm_sq y]
  -- 双线性展开 ⟪x+y, x+y⟫ = ⟪x,x⟫ + ⟪x,y⟫ + ⟪y,x⟫ + ⟪y,y⟫
  rw [inner_add_add_self]
  -- 实内积对称：⟪y,x⟫ = ⟪x,y⟫
  rw [real_inner_comm y x]
  -- 把正交条件改写成目标里出现的 ⟪y,x⟫ = 0
  have h' : ⟪y, x⟫ = 0 := by rw [real_inner_comm, h]
  rw [h']
  ring

/-! ## 版本 3：坐标平面 ℝ² 中的勾股定理

直角边向量 `(a, b)` 与 `(c, d)` 正交即 `a*c + b*d = 0`，
斜边向量是 `(a+c, b+d)`，结论就是两坐标分量的平方和相等。
这里不经过内积空间，直接用环运算和 `linear_combination`。
-/
theorem pythagoras_plane (a b c d : ℝ) (h : a * c + b * d = 0) :
    (a + c) ^ 2 + (b + d) ^ 2 = (a ^ 2 + b ^ 2) + (c ^ 2 + d ^ 2) := by
  -- 展开后差值恰好是 2 * (a*c + b*d)，由 h 为 0
  linear_combination 2 * h

/-! ## 版本 4：欧氏平面里"三角形"形式的勾股定理

设 `p₁ p₂ p₃` 是欧氏空间中的三点，`p₂` 处的角 `∠ p₁ p₂ p₃` 是直角（π/2），
则 `dist p₁ p₃² = dist p₁ p₂² + dist p₃ p₂²`。
这里我们自己从向量版推出来，而不是调用 Mathlib 的现成定理。
-/
theorem pythagoras_sub (x y : V) (h : ⟪x, y⟫ = 0) :
    ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_sub_sq_real, h]
  ring

open scoped EuclideanGeometry in
theorem pythagoras_triangle {P : Type*} [MetricSpace P] [NormedAddTorsor V P]
    (p₁ p₂ p₃ : P) (h : ∠ p₁ p₂ p₃ = Real.pi / 2) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ := by
  -- 三边长度换成向量范数：dist a b = ‖a -ᵥ b‖
  rw [dist_eq_norm_vsub V p₁ p₃, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₃ p₂,
      ← sq, ← sq, ← sq]
  -- 关键恒等式：p₁ -ᵥ p₃ = (p₁ -ᵥ p₂) - (p₃ -ᵥ p₂)
  have hv : p₁ -ᵥ p₃ = (p₁ -ᵥ p₂) - (p₃ -ᵥ p₂) := by
    rw [← vsub_sub_vsub_cancel_right p₁ p₂ p₃, ← neg_vsub_eq_vsub_rev p₂ p₃]
    abel
  rw [hv]
  -- 直角 ⟺ 两个直角边向量的内积为零
  have hinner : ⟪p₁ -ᵥ p₂, p₃ -ᵥ p₂⟫ = 0 := by
    rw [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    exact h
  -- 套用向量版（减法形式）
  exact pythagoras_sub (p₁ -ᵥ p₂) (p₃ -ᵥ p₂) hinner

/-! ## 具体数值：3-4-5 直角三角形 -/
example : ‖(EuclideanSpace.single (0 : Fin 2) (3:ℝ)) + (EuclideanSpace.single 1 (4:ℝ))‖ ^ 2
    = 3 ^ 2 + 4 ^ 2 := by
  rw [norm_add_sq_real]
  simp [PiLp.inner_apply, EuclideanSpace.single]

-- 核对公理依赖
#print axioms pythagoras
#print axioms pythagoras_plane
#print axioms pythagoras_triangle
