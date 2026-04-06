import Mathlib.NumberTheory.LSeries.RiemannZeta

#check riemannZeta

#check (riemannZeta 3).re

noncomputable def oddZeta : ℕ → ℝ := fun n ↦ (riemannZeta (2 * n + 3)).re

#check Set.range oddZeta

-- This is the goal. The dimension of the Q-vector space spanned by the set of
-- all zeta(2 k +1)$ is of infinite dimension

lemma not_fg_rat_span_range_oddZeta : ¬ (Submodule.span ℚ (Set.range oddZeta)).FG := sorry
