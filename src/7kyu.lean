import topology.metric_space.basic

def converges_to {X : Type*} [metric_space X] (s : ℕ → X) (x : X) :=
∀ (ε : ℝ) (hε : 0 < ε), ∃ N : ℕ, ∀ (n : ℕ) (hn : N ≤ n), dist x (s n) < ε

notation s ` ⟶ ` x := converges_to s x

--12
theorem limit_unique {X : Type*} [metric_space X] {s : ℕ → X}
  (x₀ x₁ : X) (h₀ : s ⟶ x₀) (h₁ : s ⟶ x₁) :
x₀ = x₁ :=
begin
  refine classical.by_contradiction _,
  intro h,
  have new_h := dist_pos.mpr h,
  rcases h₀ ((dist x₀ x₁)/2) (by linarith) with ⟨N,hN⟩,
  rcases h₁ ((dist x₀ x₁)/2) (by linarith) with ⟨N',hN'⟩,
  have nesda := dist_triangle_right x₀ x₁ (s (max N N')),
  have ans := add_lt_add (hN (max N N') (le_max_left _ _)) (hN' (max N N') (le_max_right _ _)),
  linarith
end
