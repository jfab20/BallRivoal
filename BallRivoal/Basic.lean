import Mathlib.NumberTheory.LSeries.RiemannZeta

#check riemannZeta

#check (riemannZeta 3).re

noncomputable def oddZeta : ℕ → ℝ := fun n ↦ (riemannZeta (2 * n + 3)).re

#check Set.range oddZeta

lemma not_fg_rat_span_range_oddZeta : ¬ (Submodule.span ℚ (Set.range oddZeta)).FG := sorry
