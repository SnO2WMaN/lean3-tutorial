import data.real.basic

example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
begin
  rw mul_comm a b,
  rw mul_assoc b a c,
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw ← mul_assoc a b c,
  rw mul_comm a b,
  rw mul_assoc b a c,
end

example {a b c : ℝ} : a * (b * c) = b * (a * c) := by ring

example {a b c d : ℝ} (h₁ : c = d*a + b) (h₂ : b = a*d) : c = 2*a*d :=
begin
  rw h₂ at h₁,
  rw mul_comm d a at h₁,
  rw ← two_mul (a * d) at h₁,
  rw ← mul_assoc 2 a d at h₁,
  exact h₁,
end

example {a b c d : ℝ} (h₁ : c = d*a + b) (h₂ : b = a*d) : c = 2*a*d :=
begin
  rw [h₂, mul_comm d a, ← two_mul, ← mul_assoc] at h₁,
  exact h₁,
end

example {a b c d : ℝ} (h₁ : c = d*a + b) (h₂ : b = a*d) : c = 2*a*d :=
begin
  calc 
    c   = d*a + b   : by {rw h₁}
    ... = d*a + a*d : by {rw h₂}
    ... = a*d + a*d : by {rw mul_comm d a}
    ... = 2*(a*d)   : by {rw two_mul}
    ... = 2*a*d     : by {rw mul_assoc},
end

example {a b c d : ℝ} (h₁ : c = d*a + b) (h₂ : b = a*d) : c = 2*a*d :=
begin
  calc 
    c   = d*a + b   : by {rw h₁}
    ... = d*a + a*d : by {rw h₂}
    ... = 2*a*d     : by {ring},
end

example {a b c d : ℝ} (h₁ : c = b*a - d) (h₂ : d = a*b) : c = 0 :=
begin
  rw [h₂, mul_comm b a, sub_self] at h₁,
  exact h₁,
end

example {a b c d : ℝ} (h₁ : c = b*a - d) (h₂ : d = a*b) : c = 0 :=
begin
  calc
    c   = b*a - d   : by {rw h₁}
    ... = b*a - a*b : by {rw h₂}
    ... = b*a - b*a : by {rw mul_comm}
    ... = 0         : by {rw sub_self},
end

example {a b : ℝ} : (a + b) + a = 2*a + b := by ring

-- 省略．
example (a b : ℝ) : (a + b)*(a - b) = a^2 - b^2 := by ring

