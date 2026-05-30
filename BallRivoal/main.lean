import Mathlib

open Polynomial
open Filter Topology
open Complex

variable (a : ℕ)
variable (r : ℕ)

structure hypotheses (a r : ℕ) : Prop where
  hodd_a  : Odd a
  h3_le_a  : 3 ≤ a
  h1_le_r  : 1 ≤ r
  h2r_le_a : 2 * r < a

noncomputable def R (n : ℕ) (z : ℂ) : ℂ :=
  (n.factorial ^ (a - 2 * r) : ℂ) * 
  (ascPochhammer ℂ (r * n)).eval (z - (r * n) + 1) *
  (ascPochhammer ℂ (r * n)).eval (z + n + 2) /
  ((ascPochhammer ℂ (n + 1)).eval (z + 1))^(a)

-- With a = 3 and r = 1, we have R_0 (1) = 1/8
-- theorem h : R 3 1 0 1 = 1/8 := by
--   unfold R
--   norm_num

noncomputable def S (n : ℕ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, R a r n k / (z^k)

-- To define c_(l,j,n), we need to remove the pole at z = -(j+1).
-- So I define the numerator / denominator of R_n (z)

noncomputable def Rnum (n: ℕ) (z: ℂ) : ℂ := 
  (n.factorial ^ (a - 2 * r) : ℂ) *
  (ascPochhammer ℂ (r * n)).eval (z - (r * n) + 1) *
  (ascPochhammer ℂ (r * n)).eval (z + n + 2)


noncomputable def Rdenom_without_z_plus_j_plus_one (n j: ℕ) (z : ℂ)
  : ℂ :=
  ∏ k ∈ (Finset.range (n+1)).erase j , (z + 1 + k)^a


noncomputable def c (l j n : ℕ) : ℂ :=
  let f := fun (z : ℂ) ↦ (Rnum a r n z) / (Rdenom_without_z_plus_j_plus_one a n j z)
  iteratedDeriv (a - l) f (-(j + 1)) / ((a - l).factorial : ℂ)

-- computing an explicit value: a = 3 r = 1 c_(1,0,0) = 0
-- in this case R_0 (z) = 1/(z+1)^3 and c_(1,0,0) = D_2 (1/(z+1)^3 * (z+1)^3)
-- which means c_(1,0,0) = D_2 (1) = 0

theorem h: c 3 1 1 0 0 = 0 := by
  unfold c Rnum Rdenom_without_z_plus_j_plus_one
  simp
  apply iteratedDeriv_const

noncomputable def P (l n : ℕ) (z : ℂ) : ℂ :=
  if l = 0 then
    ∑ m ∈ Finset.Icc 1 a,
    ∑ j ∈ Finset.Icc 1 n,
    ∑ k ∈ Finset.range j,
    - (c a r m j n) / ((k + 1 : ℂ))^m * z^(j-k)
  else
    ∑ j ∈ Finset.range (n+1) , c a r l j n * z^j

theorem lemma_nesterenko : 1 = 1 := by
  norm_num

theorem lemma2p1 (h: hypotheses a r) (n : ℕ) :
    S a r n 1 =
    P a r 0 n 1
    + ∑ l ∈ Finset.Icc 2 a, P a r l n 1 * riemannZeta (↑ l) := by 
    sorry

lemma conditions_for_pln_eq_zero (n : ℕ) (l : ℕ)
  (hl_lower_bound: 1 ≤ l)
  (hl_upperbound : l ≤ a)
  (hfor_zero_polynomial: Odd ( (n + 1) * a + l)) :
  P a r l n = 0
   := by
  sorry

lemma sn1_linear_combination_odd_zeta_values (n : ℕ)
  (hn_even: Even n)  : 
    S a r n 1  = P a r 0 n 1 + 
    ∑ k ∈ Finset.Icc 1 ((a-1)/2) , (P a r (2 * k + 1) n 1) * riemannZeta (↑ (2 * k + 1) ) := by 
    sorry

def Q (x : ℝ) : ℝ := 
  r * x^(a + 2) - (r + 1) * x^(a + 1) + (r + 1) * x - r

lemma exists_unique_root_Q (h: hypotheses a r) :
    ∃! s ∈ Set.Ioo (0 : ℝ) 1, Q a r s = 0 := by 
    sorry

noncomputable def s0 (h: hypotheses a r): ℝ :=
  Classical.choose (exists_unique_root_Q a r h)

noncomputable def phi (h: hypotheses a r): ℝ := 
  let s := s0 a r h
  ((r+1)*s - r)^r * ((r+1) - r*s )^(r + 1) * (1-s)^(a - 2 * r)

lemma lim_sn_pow_one_over_n_eq_phi (h: hypotheses a r) : 
    let f : ℕ → ℝ := fun n => ((‖S a r n 1‖)^((1: ℝ)/(↑n)))
    Tendsto f atTop (𝓝  (phi a r h) ) := by
    sorry

lemma bounds_on_phi (h: hypotheses a r) : 
    let phi := phi a r h
    0 < phi ∧ phi ≤ 2^(r + 1) / r^(a - 2 * r) := by
    sorry

lemma limsup_pln_pow_one_over_n (h : hypotheses a r) (l : ℕ)
  (hl_upperbound : l ≤ a) :
  Filter.limsup (fun n => ( (‖P a r l n 1‖)^(1/(↑n)))) atTop 
  ≤ 2^(a - 2 * r) * (2 * r + 1)^(2 * r +1) := by 
  sorry

-- There are (a-1)/2 numbers in zeta(3), dots, zeta(a)
-- Fin ((a-1)/2) = {0,..., (a-1)/2 - 1} so x -> 2 * x + 3 maps
-- it to 3, ..., a

noncomputable def first_odd_zeta_values (a : ℕ): Fin ((a-1)/2) → ℝ := fun n ↦ (riemannZeta (2 * n + 3)).re

-- dimension (a) = dim_Q vect Q 1,zeta(3), dots, zeta(a)

noncomputable def dimension_span_first_odd_values_zeta (a : ℕ) :=
    Module.finrank ℚ (Submodule.span ℚ (
    {1} ∪ Set.range (first_odd_zeta_values a)
    ))

lemma lower_bound_dimension (h : hypotheses a r) :
    dimension_span_first_odd_values_zeta a ≥ 
    (
      (a-2 * r) * (Real.log 2) + 
      (2 * r + 1)* (Real.log (2 *r + 1))
      - (Real.log (phi a r h) )
    )/(
    a + (a - 2 * r) * (Real.log 2) 
    + (2 * r + 1) * (Real.log (2 * r + 1))
    ) := by
  sorry

lemma cor_lower_bound_dimension (h: hypotheses a r) :
    dimension_span_first_odd_values_zeta a ≥ 
    (
      (Real.log r) + (a-r)/(a+1) * (Real.log 2)
    )/(
    1 + (Real.log 2) + 
    (2 * r + 1) / (a + 1) * (Real.log (r+1))
    ) := by
  sorry

theorem two_linearly_independent_values_before_169 :
    ∃ (j: ℕ) , 
    Odd j ∧
    j ≤ 169
    ∧
    3 ≤
    Module.finrank ℚ (Submodule.span ℚ (
    {1} ∪ {(riemannZeta 3).re} ∪ {(riemannZeta j).re}
    ))
    := by 
    sorry

-- I need to remove a hypotheses here, as I just need a ≥ 3 odd

theorem dimension_at_least_log_over_3 (h: hypotheses a r) :
    dimension_span_first_odd_values_zeta a ≥ 1/3 * (Real.log a) :=
  by 
  sorry

theorem dimension_asymptotic_bound (h: hypotheses a r) :
    ∀ ε > 0, ∃ N , ∀ a > N, 
    dimension_span_first_odd_values_zeta a ≥ 
    (1-ε)/(1 + (Real.log 2)) * (Real.log a)
    := by
  sorry
