/-
 These are my solutions to the katas in the Mathematical Analysis collection in Codewars (https://www.codewars.com/collections/mathematical-analysis).
-/

import data.real.basic
import data.real.basic data.set.intervals.basic
open classical
attribute [instance] prop_decidable

/-
  Rigorous definition of a limit
  For a sequence x_n, we say that \lim_{n \to \infty} x_n = l if
    ∀ ε > 0, ∃ N, n ≥ N → |x_n - l| < ε
-/

def lim_to_inf (x : ℕ → ℝ) (l : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (x n - l) < ε

/-
 Suppose `xₙ ≤ l ≤ yₙ` and the limit of `xₙ - yₙ` is `0` as `n → ∞`. Then we have the limit of `xₙ` is equal to the limit of `yₙ` which equals to `l` as `n → ∞`.
-/

--08 (6 kyu)
theorem exercise_1p2 (x y : ℕ → ℝ) (l : ℝ)
  (h₁ : ∀ n, x n ≤ l ∧ l ≤ y n)
  (h₂ : lim_to_inf (λ n, x n - y n) 0) :
  lim_to_inf x l ∧ lim_to_inf y l :=
begin
 split;
 try { 
    intros ε h,
    rcases h₂ ε h with ⟨N,hN⟩,
    use N,
    intros n hn,
    specialize hN n hn,
    specialize h₁ n,
    have := sub_le_sub h₁.1 h₁.2,
    have H : x n - l ≤ y n - x n := by linarith,
    have H' : y n - l ≤ y n - x n := by linarith,
    have hH' : abs (y n - l) ≤ abs (x n - y n),
     simp [←abs_neg (x n - y n)],
     apply abs_le_abs H' _,
     linarith,
    have hH : abs (x n - l) ≤ abs (x n - y n),
     simp [←abs_neg (x n - y n)],
     apply abs_le_abs H _,
     linarith,
    simp at hN,
    linarith
  }
end

/-
 Suppose `|xₙ - l| ≤ yₙ` and `lim_{n → ∞} yₙ = 0`. Then we have `lim_{n → ∞} xₙ = l`.
-/

--09 (7 kyu)
theorem exercise_1p3 (x y : ℕ → ℝ) (l : ℝ)
  (h₁ : ∀ n, abs (x n - l) ≤ y n) (h₂ : lim_to_inf y 0) :
  lim_to_inf x l :=
begin
 intros ε h,
 rcases h₂ ε h with ⟨N,hN⟩,
 use N,
 intros n hn,
 specialize hN n hn,
 specialize h₁ n,
 simp at hN,
 calc abs (x n - l) ≤ y n       : by assumption
                ... ≤ abs (y n) : le_max_left (y n) (-y n)
                ... < ε         : by assumption
end

/-
 Suppose `lim_{n → ∞} xₙ = l`. Then we have `lim_{n → ∞} |xₙ| = |l|`. 
-/

--10 (7 kyu)
theorem exercise_1p4 (x : ℕ → ℝ) (l : ℝ) (h₁ : lim_to_inf x l) :
  lim_to_inf (λ n, abs (x n)) (abs l) :=
begin
  intros ε h,
  rcases h₁ ε h with ⟨N,hN⟩,
  use N,
  intros n hn,
  specialize hN n hn,
  dsimp,
  linarith [abs_abs_sub_abs_le_abs_sub (x n) l],
end

/-
 Suppose `lim_{n → ∞} xₙ = l` and `lim_{n → ∞} yₙ = k`, then we have `lim_{n → ∞} max {xₙ, yₙ} = max {l, k}` and `lim_{n → ∞} min {xₙ, yₙ} = min {l, k}`. 
-/

--11 (5 kyu)
theorem exercise_1p18 (x y : ℕ → ℝ) (l k : ℝ) (h₁ : lim_to_inf x l)
  (h₂ : lim_to_inf y k)  : lim_to_inf (λ n, max (x n) (y n)) (max l k) ∧
  lim_to_inf (λ n, min (x n) (y n)) (min l k) :=
begin
  split,
   { intros ε hε,
     cases h₁ ε hε with N hN,
     cases h₂ ε hε with N' hN',
     use max N N',
     intros n hn,
     dsimp,
    have HH := abs_max_sub_max_le_max (x n) (y n) l k,
    specialize hN n (by linarith [le_max_left N N']),
    specialize hN' n (by linarith [le_max_right N N']),
    cases max_cases (abs(x n - l)) (abs(y n - k)) with lH rH,
     { calc abs(max (x n) (y n) - max l k) ≤ max (abs(x n - l)) (abs(y n - k)) : HH 
                                      ... = abs(x n - l) : lH.1
                                      ... < ε : hN },
     { calc abs(max (x n) (y n) - max l k) ≤ max (abs(x n - l)) (abs(y n - k)) : HH
                                       ... = abs(y n - k) : rH.1
                                       ... < ε : hN' } },
   { intros ε hε,
     cases h₁ ε hε with N hN,
     cases h₂ ε hε with N' hN',
     use max N N',
     intros n hn,
     dsimp,
     have HH := abs_min_sub_min_le_max (x n) (y n) l k,
     specialize hN n (by linarith [le_max_left N N']),
     specialize hN' n (by linarith [le_max_right N N']),
     cases max_cases (abs(x n - l)) (abs(y n - k)) with lH rH,
      { calc abs(min (x n) (y n) - min l k) ≤ max (abs(x n - l)) (abs(y n - k)) : HH
                                        ... = abs (x n - l) : lH.1
                                        ... < ε : hN, },
      { calc abs(min (x n) (y n) - min l k) ≤ max (abs(x n - l)) (abs(y n - k)) : HH
                                        ... = abs (y n - k) : rH.1
                                        ... < ε : hN' } }
end

open set

/-
  Continuous function
  A function f(x) is said to be continuous at x = a if, for any ε > 0,
  there is δ > 0 s.t. |f(x) - f(a)| < ε whenever |x - a| < δ
-/

def continuous_at (f : ℝ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - f a) < ε

--13 (6 kyu)
theorem continuous_function_about_an_open_interval {f a}
  (hcont : continuous_at f a) (hgt : f a > 0) :
  ∃ b c : ℝ, a ∈ Ioo b c ∧ ∀ x ∈ Ioo b c, f x > 0 :=
begin
  rcases hcont ((f a)/2) (by linarith) with ⟨δ,hδ,h'⟩,
  use a - δ,
  use a + δ,
  split,
   { exact ⟨sub_lt_self a hδ,lt_add_of_pos_right a hδ⟩ },
   { intros x hx,
     simp [Ioo_def] at hx,
     cases hx,
     have hh : x - a > -δ := by linarith,
     have hh2 : x - a < δ := by linarith,
     have hh3 : abs (x - a) < δ,
      refine max_lt hh2 _,
      exact neg_lt.mp hh,
     specialize h' x (by linarith),
     rw abs_lt at h',
     cases h',
     linarith }
end
