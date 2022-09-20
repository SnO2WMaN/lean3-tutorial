-- 実数のインポート
import data.real.basic

import tactic.suggest

-- 排中律を認める
noncomputable theory
open_locale classical

universe u

-- mathlibの実数の上界の定義
#check upper_bounds

-- 実数の集合の上界の集合
def up_bounds (A : set ℝ) := { x : ℝ | ∀ a ∈ A, a ≤ x }

def is_maximum (a : ℝ) (A : set ℝ) := a ∈ A ∧ a ∈ up_bounds A
infix ` is_a_max_of `:55 := is_maximum

-- 実数の集合はただ一つの最大値を持つ．
lemma unique_max {A : set ℝ} {x y : ℝ} (hx : x is_a_max_of A) (hy : y is_a_max_of A) : x = y :=
begin
  cases hx with x_in x_up,
  cases hy with y_in y_up,
  
  specialize x_up y,
  specialize x_up y_in,

  specialize y_up x,
  specialize y_up x_in,

  -- x ≤ y かつ y ≤ x ならば x = y
  linarith,
end

-- unique_maxの証明は次のようにも書ける．
example (A : set ℝ) (x y : ℝ) (hx : x is_a_max_of A) (hy : y is_a_max_of A) : x = y :=
begin
  have : x ≤ y := hy.2 x hx.1,
  have : y ≤ x := hx.2 y hy.1,
  linarith,
end 

-- unique_maxの証明は次のようにも書ける．(2)
example (A : set ℝ) (x y : ℝ) (hx : x is_a_max_of A) (hy : y is_a_max_of A) : x = y :=
  le_antisymm (hy.2 x hx.1) (hx.2 y hy.1)

-- 実数の下界の集合
def low_bounds (A : set ℝ) := { x : ℝ | ∀ a ∈ A, x ≤ a}

-- infimum（下限）
def is_inf (x : ℝ) (A : set ℝ) := x is_a_max_of (low_bounds A)
infix ` is_an_inf_of `:55 := is_inf

-- Aの下限より大きい数は，あるAの要素より大きい数である
lemma inf_lt {A : set ℝ} {x : ℝ} (hx : x is_an_inf_of A) : ∀ y, x < y → ∃ a ∈ A, a < y :=
begin
  intro y,
  -- 対偶を示す
  contrapose, 
  -- ¬∃を∀に変換
  push_neg,
  intro h, -- `h`は，`A`の下界が`y`であると主張している．
  exact hx.2 y h,
end

-- `contrapose`と`push_neg`は`contrapose!`で略すこともできる．


-- すべての正の`ε`に対して`y ≤ x + ε`ならば，`y ≤ x`
lemma le_of_le_add_eps {x y : ℝ} : (∀ ε > 0, y ≤ x + ε) → y ≤ x := 
begin
  contrapose!,
  intro h,
  -- ある`ε`について，`((y - x) / 2)`を代入
  use ((y - x) / 2),
  split,
  linarith,
  linarith,
end

example {x y : ℝ} : (∀ ε > 0, y ≤ x + ε) →  y ≤ x := 
begin
  contrapose!,
  exact assume h, ⟨(y-x)/2, by linarith, by linarith⟩, 
  -- `∃ z, P z`の証明は，`z₀`の構成と，`P z₀`の証明の複合で成り立つ．これを`⟨z₀, h⟩`と表記する．
  -- `P ∧ Q`の証明も同様に`⟨P, Q⟩`と表記する．
  -- `⟨z₀, ⟨h₁, h₂⟩⟩`は右結合性より`⟨z₀, h₁, h₂⟩`と書ける．
end

-- `begin`/`end`は更に`by`を用いて次のように省略できる．
example {x y : ℝ} : (∀ ε > 0, y ≤ x + ε) →  y ≤ x := 
  by {contrapose!, exact assume h, ⟨(y-x)/2, by linarith, by linarith⟩}

example {x y : ℝ} : (∀ ε > 0, y ≤ x + ε) →  y ≤ x := 
begin
  intro h,
  -- 背理法
  by_contradiction H,
  push_neg at H,
  have key := calc
    y   ≤ x + (y - x)/2 : h _ (by linarith)
    ... = x/2 + y/2     : by ring -- 環の性質より
    ... < y             : by linarith, -- 線形性の性質より 
  -- linarith
  apply lt_irrefl y,
  exact key,
end

-- 絶対値
local notation `|`x`|` := abs x

-- 実数列の収束について．実数列`u`の極限は`l`に収束する．
-- `(u n)`は数列`u`の`n`番目の項を指す．
def limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |(u n) - l| ≤ ε

-- 実数列uのすべてのn番目の項以下なら，極限値よりも小さい．
lemma le_lim {x y : ℝ} {u : ℕ → ℝ} (hu : limit u x) (ineq : ∀ n, y ≤ (u n)) : y ≤ x :=
begin
  apply le_of_le_add_eps,
  intros ε ε_pos,
  cases hu ε ε_pos with N HN,
  calc
    y   ≤ (u N)         : ineq N
    ... = x + ((u N) - x) : by linarith
    ... ≤ x + |(u N) - x| : add_le_add (by linarith) (by library_search) --- `library_search`で適した定理や補題を自動で持ってくる
    ... ≤ x + ε           : add_le_add (by linarith) (HN N (by linarith)),
end

-- `(n + 1 : ℝ)`で自然数(ℕ)`n + 1`を実数(ℝ)に変換していることに注意．
lemma inv_suc_pos : ∀ n : ℕ, 1 / (n + 1 : ℝ) > 0 :=
begin
  intro n,
  suffices : (n + 1 : ℝ) > 0,
  { library_search }, -- 正の数の逆数は正であるという主張の補題を自動補完
  norm_cast, -- 自然数についての主張に戻す
  linarith,
end

example : ∀ n : ℕ, 1/(n+1 : ℝ) > 0 :=
  λ n, one_div_pos.mpr (by exact_mod_cast nat.succ_pos n)

lemma limit_inv_succ : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, (1 / (n + 1 : ℝ)) ≤ ε :=
begin
  intros ε ε_pos,
  suffices : ∃ N : ℕ, 1 / ε ≤ N,
  {
    cases this with N HN,
    use N,
    intros n Hn,
    rw [div_le_iff', ← div_le_iff ε_pos],
    replace Hn : (N : ℝ) ≤ n, exact_mod_cast Hn,
    linarith,
    exact_mod_cast (nat.succ_pos n),
  },
  -- exact exists_nat_ge (1 / ε)
  exact archimedean_iff_nat_le.1 (by apply_instance) (1/ε),
end

lemma inf_seq (A : set ℝ) (x : ℝ) :
  (x is_an_inf_of A) ↔ (x ∈ low_bounds A ∧ (∃ u : ℕ → ℝ, ((limit u x) ∧ (∀ n, u n ∈ A)))) :=
begin
  split,
  {
    intro h,
    split,
    { exact h.1 },
    have key : ∀ n : ℕ, ∃ a ∈ A, a < x + 1/(n + 1),
    {
      intro n,
      apply inf_lt h,
      have : 0 < 1/(n+1:ℝ), from inv_suc_pos n,
      linarith,
    },
    {
      choose u hu using key, -- 選択公理
      use u,
      split,
      {
        intros ε ε_pos,
        cases (limit_inv_succ ε ε_pos) with N H,
        use N,
        intros n hn,
        have : x ≤ (u n), from h.1 _ (hu n).1,
        have : (u n) < x + ε := calc
          u n < x + 1/(n + 1) : (hu n).2
          ... ≤ x + ε         : add_le_add (le_refl x) (H n hn),
        rw abs_of_nonneg,
        linarith, 
        linarith, 
      },
      {
        intro n,
        exact (hu n).1,
      },
    }
  },
  {
    intro h,
    rcases h with ⟨ x_min, u, lim, huA⟩, 
    fconstructor,
    exact x_min,
    intros y y_mino,
    apply le_lim lim,
    intro n,
    exact y_mino (u n) (huA n),
  },
end