import Mathlib.NumberTheory.LSeries.RiemannZeta

#check riemannZeta

#check (riemannZeta 3).re

noncomputable def oddZeta : ℕ → ℝ := fun n ↦ (riemannZeta (2 * n + 3)).re

#check Set.range oddZeta

-- This is the goal. The dimension of the Q-vector space spanned by the set of
-- all zeta(2 k +1)$ is of infinite dimension

lemma not_fg_rat_span_range_oddZeta : ¬ (Submodule.span ℚ (Set.range oddZeta)).FG
:= sorry

-- reste à savoir faire des sommes, des dimension et des log
lemma nesterenko : ∀ N : ℕ, ∀ (θ: {n : ℕ | 1 ≤ n ∧ n ≤ N} → ℝ), ∀ α β:ℝ,
∀ (p:{n : ℕ | 1 ≤ n ∧ n ≤ N}×ℕ→ℤ), ∀ f g : ℕ → ℝ,
((0<α ∧ α<1 ∧ 1<β)
∧(∀ε>0, ∃Nf Ng : ℕ, ∃C D :ℝ , ∀n>Nf, |f n|<ε*C*n ∧ |g n|<ε*D*n)
∧(∀ n : ℕ, ∀ l : {n : ℕ | 1 ≤ n ∧ n ≤ N}, ∀ε>0, |p (l, n)|≤β^(n+g n))
→ true)
:= sorry
