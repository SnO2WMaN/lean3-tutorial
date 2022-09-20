import data.real.basic
--- sub_nonneg {x y : ℝ} : 0 ≤ y - x ↔ x ≤ y

example {a b c : ℝ} (hab : a ≤ b) : c + a ≤ c + b :=
begin
  rw ← sub_nonneg,
  have key : (c + b) - (c + a) = b - a, by {ring},
  rw key,
  rw sub_nonneg,
  exact hab,
end
 
example {a b c : ℝ} (hab : a ≤ b) : c + a ≤ c + b := 
begin 
  apply add_le_add_left hab,
end

example {a b : ℝ} (ha : 0 ≤ a) : b ≤ a + b :=
begin
  calc
    b   = 0 + b : by {ring}
    ... ≤ a + b : by {exact add_le_add_right ha b},
end

example {a b : ℝ} (hb: 0 ≤ b) : a ≤ a + b :=
begin
  calc
    a   = a + 0 : by {ring}
    ... ≤ a + b : by {exact add_le_add_left hb a},
end


-- le_add_of_nonneg_left  {a b : ℝ} (ha : 0 ≤ a) : b ≤ a + b
-- le_add_of_nonneg_right {a b : ℝ} (hb : 0 ≤ b) : a ≤ a + b
example {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
begin
  calc  
    0   ≤ a     : ha
    ... ≤ a + b : le_add_of_nonneg_right hb,
end

example {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d :=
begin
  calc
    a + c ≤ b + c : by {exact add_le_add_right hab c}
    ...   ≤ b + d : by {exact add_le_add_left hcd b},
end

example {a b c : ℝ} (hc : 0 ≤ c) (hab : a ≤ b) : a*c ≤ b*c :=
begin
  rw ← sub_nonneg,
  have key : b * c - a * c = (b - a) * c := by ring,
  rw key,
  apply mul_nonneg, -- {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x*y
  {
    rw sub_nonneg,
    exact hab,
  },
  {
    exact hc
  }
end

example {a b c : ℝ} (hc : 0 ≤ c) (hab : a ≤ b) : a*c ≤ b*c :=
begin
  have hab' : 0 ≤ b - a, {rwa ← sub_nonneg at hab}, -- `rw ← sub_nonneg at hab; exact hab`
  have h₁ : 0 ≤ (b-a)*c, {exact mul_nonneg hab' hc},
  have h₂ : (b-a)*c = b*c - a*c, by ring,
  have h₃ : 0 ≤ b*c - a*c, by rwa h₂ at h₁,
  rwa sub_nonneg at h₃,
end

example {a b c : ℝ} (hc : 0 ≤ c) (hab : a ≤ b) : a*c ≤ b*c :=
begin
  rw ← sub_nonneg,
  calc
    0   ≤ (b-a)*c   : mul_nonneg (by rwa sub_nonneg) hc
    ... = b*c - a*c : by ring,
end

example {a b c : ℝ} (hc : c ≤ 0) (hab : a ≤ b) : b*c ≤ a*c :=
begin
  rw ← sub_nonpos at hab,
  rw ← sub_nonneg,
  have key : a * c - b * c = (a - b) * c := by ring,
  rw key,
  exact (mul_nonneg_of_nonpos_of_nonpos hab hc), 
end

-- le_add_of_nonneg_left (a b : ℝ) : 0 ≤ a → b ≤ a + b
example {a b : ℝ} : 0 ≤ a → b ≤ a + b := le_add_of_nonneg_left

example {a b : ℝ} : 0 ≤ b → a ≤ a + b := 
begin
  intros h,
  calc
    a   = a + 0 : by {ring}
    ... ≤ a + b : by {exact add_le_add_left h a},
end

example {a b : ℝ} : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b :=
begin
  intros h,
  cases h with ha hb,
  exact add_nonneg ha hb,
end

example {a b : ℝ} : 0 ≤ a → 0 ≤ b → (0 ≤ a + b) := add_nonneg

example {a b : ℝ} (H : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b) : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) :=
begin
  intros ha hb,
  apply H,
  split,
  exact ha,
  exact hb,
end

example (P Q R : Prop) : P ∧ Q → Q ∧ P :=
begin
  intro h,
  cases h with hp hq,
  split,
  exact hq,
  exact hp,
end

example {a b : ℝ} (H : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b) : 0 ≤ a → (0 ≤ b → 0 ≤ a + b) :=
begin
  intros ha hb,
  exact H ⟨ ha, hb ⟩,
end

example (P Q R : Prop): P ∧ Q → Q ∧ P :=
begin
  rintros ⟨h₁, h₂⟩,
  exact ⟨h₂, h₁⟩,
end

example {P Q R : Prop} : (P ∧ Q → R) ↔ (P → Q → R) :=
begin
  split,
  intros h,
  intros hp hq,
  apply h,
  split,
  exact hp,
  exact hq,

  intros h,
  intros hpq,
  cases hpq with hp hq,
  apply h,
  exact hp,
  exact hq,
end


example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b :=
begin
  linarith,
end