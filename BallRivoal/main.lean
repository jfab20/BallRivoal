import Mathlib

open Polynomial
open Filter Topology
open Complex
open Asymptotics

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

-- theorem h: c 3 1 1 0 0 = 0 := by
--   unfold c Rnum Rdenom_without_z_plus_j_plus_one
--   simp
--   apply iteratedDeriv_const

noncomputable def P (l n : ℕ) : ℂ[X] :=
  if l = 0 then
    ∑ m ∈ Finset.Icc 1 a,
    ∑ j ∈ Finset.Icc 1 n,
    ∑ k ∈ Finset.range j,
    C (- (c a r m j n) / ((k + 1 : ℂ))^m) * X^(j-k)
  else
    ∑ j ∈ Finset.range (n+1) , C (c a r l j n ) * X^j

theorem nesterenko
  (N : ℕ)
  (θ : Fin N → ℝ)
  (p : Fin N → ℕ → ℤ)
  (f g : ℕ → ℝ)
  (α β : ℝ)
  (α0 : 0<α)
  (β1 : 1<β)
  (hf : ∀ε>0, ∃ Nf : ℕ, ∀n>Nf, |f n|<ε*n)
  (hg : ∀ε>0, ∃ Ng : ℕ, ∀n>Ng, |g n|<ε*n)
  (h2 : ∀ n : ℕ, |∑ l, p l n * θ l| = α^(n+g n))
  (h3 : ∀ n : ℕ, ∀ l : Fin N, ∀ε>0, |p l n|≤β^(n+g n))
  :
  Set.finrank ℚ (Set.range θ)
  ≥ (Real.log β - Real.log α) / (Real.log β)
  := by sorry

theorem sn_of_one_eq_linear_combination_zeta (h: hypotheses a r) (n : ℕ) :
    S a r n 1 =
    (P a r 0 n).eval 1
    + ∑ l ∈ Finset.Icc 2 a, (P a r l n).eval 1 * riemannZeta (↑ l) := by
    sorry

lemma conditions_for_pln_of_one_eq_zero (n : ℕ) (l : ℕ)
  (hl_lower_bound: 1 ≤ l)
  (hl_upperbound : l ≤ a)
  (hfor_zero_polynomial: Odd ( (n + 1) * a + l)) :
  (P a r l n).eval 1 = 0
   := by
  sorry

lemma sn1_linear_combination_odd_zeta_values (n : ℕ)
  (hn_even: Even n)  :
    S a r n 1  = (P a r 0 n).eval 1 +
    ∑ k ∈ Finset.Icc 1 ((a-1)/2) , ((P a r (2 * k + 1) n).eval 1)
    * riemannZeta (↑ (2 * k + 1) ) := by sorry

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
    Tendsto (fun n => ((‖S a r n 1‖)^((1: ℝ)/(↑n)))) atTop (𝓝  (phi a r h) )
    := by sorry

lemma bounds_on_phi (h: hypotheses a r) :
    letI phi := phi a r h
    0 < phi ∧ phi ≤ 2^(r + 1) / r^(a - 2 * r) := by
    sorry

lemma limsup_pln_pow_one_over_n (h : hypotheses a r) (l : ℕ)
  (hl_upperbound : l ≤ a) :
  Filter.limsup (fun n => ( (‖(P a r l n).eval 1‖)^(1/(↑n)))) atTop
  ≤ 2^(a - 2 * r) * (2 * r + 1)^(2 * r +1) := by
  sorry

def lcm_of_first_n_integers (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

-- checking that dn behaves correctly

-- theorem lcm_of_first_five_integers :
--     lcm_of_first_n_integers 5 = 60 := by
--     native_decide

lemma dn_times_pln_is_integer_polynomial (l n : ℕ) (hl : l ≤ a) :
  ∃ (Q : Polynomial ℤ),
    C (((lcm_of_first_n_integers n) ^ (a - l) : ℕ) : ℂ)
    * P a r l n = Q.map (algebraMap ℤ ℂ) := by
  sorry

-- There are (a-1)/2 numbers in zeta(3), dots, zeta(a)
-- Fin ((a-1)/2) = {0,..., (a-1)/2 - 1} so x -> 2 * x + 3 maps
-- it to 3, ..., a

noncomputable def first_odd_zeta_values (a : ℕ): Fin ((a-1)/2) → ℝ :=
  fun n ↦ (riemannZeta (2 * n + 3)).re

-- dimension (a) = dim_Q vect Q 1,zeta(3), dots, zeta(a)

noncomputable def dimension_span_first_odd_values_zeta (a : ℕ) :=
    Module.finrank ℚ (Submodule.span ℚ (
    {1} ∪ Set.range (first_odd_zeta_values a)
    ))

noncomputable def second_proposition_bound (a: ℕ) (r: ℕ) : ℝ :=
    (
      (Real.log r) + (a-r)/(a+1) * (Real.log 2)
    )/(
    1 + (Real.log 2) +
    (2 * r + 1) / (a + 1) * (Real.log (r+1))
    )

lemma lower_bound_dimension (h : hypotheses a r) :
    (
      (a-2 * r) * (Real.log 2) +
      (2 * r + 1)* (Real.log (2 *r + 1))
      - (Real.log (phi a r h) )
    )/(
    a + (a - 2 * r) * (Real.log 2)
    + (2 * r + 1) * (Real.log (2 * r + 1))
    )
    ≤ dimension_span_first_odd_values_zeta a
    := by
  sorry

lemma cor_lower_bound_dimension (h: hypotheses a r) :
    second_proposition_bound a r
    ≤ dimension_span_first_odd_values_zeta a
    := by
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

theorem dimension_at_least_log_over_3 (hodd_a: Odd a) (h3_le_a: 3 ≤ a) :
    1/3 * (Real.log a) ≤
    dimension_span_first_odd_values_zeta a :=
  by
  sorry

def condFilter : Filter ℕ := atTop ⊓ principal {a | Odd a ∧ 3 ≤ a}

noncomputable def optimal_r (a : ℕ) : ℕ := ⌊a/(Real.log a)^2⌋₊

lemma bounded_difference_with_r (a: ℕ) :
    |optimal_r a - (a/(Real.log a)^2)| ≤ 1 := by

    unfold optimal_r
    apply abs_le.2
    constructor
    · simp
      apply le_of_lt
      apply ((Nat.floor_eq_iff _).1 _).2
      positivity
      tauto

    · simp
      have h0 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
      have h1 : ⌊a / Real.log ↑a ^ 2⌋₊ ≤ ↑a / Real.log ↑a ^ 2 := by
        apply ((Nat.floor_eq_iff _).1 _).1
        positivity
        tauto
      linarith [add_le_add (h0) (h1)]

lemma bounds_on_r (a : ℕ) (ha: 5 ≤ a) :
    1 ≤ optimal_r a ∧ 2 * (optimal_r a) < a := by
  constructor
  · unfold optimal_r
    apply (Nat.one_le_floor_iff _).mpr
    rw [le_div_iff₀', mul_one]
    apply (Real.sq_le _).2
    · constructor
      · calc
        -√a ≤ 0 := by
          apply neg_le_of_neg_le 
          rw [neg_zero]
          positivity
        0 ≤ Real.log a := by positivity
      · apply (Real.log_le_iff_le_exp _).2
        · have h1 : 0 ≤ √a := by
            apply le_of_lt
            apply Real.sqrt_pos.2
            norm_cast
            linarith
          have h2 := Real.sum_le_exp_of_nonneg h1 4
          apply le_trans _ h2
          have h4 : 1 + √a + (√a)^2 / 2 + (√a)^3 / 6
          = ∑ i ∈ Finset.range 4, √a^i/ (↑i.factorial) := by
            simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, _root_.pow_zero, Nat.factorial, pow_one, mul_one, Nat.mul_one, Nat.cast_succ]
            ring_nf
          rw [<- h4]
          have h5 : √a ^2 = a := by 
            apply Real.sq_sqrt
            positivity
          nth_rw 1 [<- h5]
          set x : ℝ := √a with hx
          have h6 : 0 ≤ x^2 - 3 * x + 6 := by
            have hsq : 0 ≤ (x - 3 / 2)^2 := by positivity
            nlinarith
          have h7 : 0 ≤ x^3 - 3 * x ^2 + 6 * x := by
            have hsq : 0 ≤ (x - 3 / 2)^2 := by positivity
            have hx : 0 ≤ x := by positivity
            nlinarith
          nlinarith
        · positivity
    · linarith
    · apply sq_pos_of_pos
      apply (Real.log_pos_iff ?_).mpr ?_
      linarith
      norm_cast
      linarith
  · unfold optimal_r
    have h1: 2 * ⌊a / Real.log a ^ 2⌋₊  ≤ 2 * (a / (Real.log a)^2) := by 
      have _ := Nat.floor_le (by positivity : 0 ≤ (a : ℝ) / Real.log a ^ 2)
      linarith
    have h2 : 2 * (a / Real.log a ^ 2) < (a : ℝ) := by
      field_simp
      apply (div_lt_iff₀ _).mpr
      · rw [one_mul]
        have h2: 2 < Real.log 5 ^2 := by 
          have _ := Real.log_five_gt_d9
          nlinarith
        have h3: Real.log 5 ^2 ≤ Real.log a ^2 := by
            gcongr
            norm_cast
        linarith

      · apply sq_pos_of_pos
        apply (Real.log_pos_iff ?_).mpr ?_
        linarith
        norm_cast
        linarith

    exact_mod_cast lt_of_le_of_lt h1 h2


noncomputable def lower_bound_on_optimal_r (a: ℕ) : ℝ :=
  second_proposition_bound a (optimal_r a)

lemma applying_corollary_to_r (a: ℕ) (hodd : Odd a) (h3lea: 3 ≤ a):
     lower_bound_on_optimal_r a ≤ dimension_span_first_odd_values_zeta a  := by

  by_cases ha: a = 3
  · subst ha
    unfold lower_bound_on_optimal_r second_proposition_bound optimal_r
    unfold dimension_span_first_odd_values_zeta
    push_cast
    have h_floor : ⌊3 / Real.log 3 ^ 2⌋₊ = 2 := by
       apply (Nat.floor_eq_iff ?_).mpr ?_
       positivity
       constructor
       · field_simp
         have _ := Real.log_three_lt_d9
         calc 
          2 * Real.log 3 ^ 2 ≤ 2 * (1.0986122888)^2 := by gcongr
          _ ≤ 3 := by norm_num
       · norm_num
         field_simp
         apply (one_lt_sq_iff₀ ?_).mpr ?_
         positivity
         apply (Real.lt_log_iff_exp_lt _).mpr
         · linarith [Real.exp_one_lt_d9]
         · linarith
    rw [h_floor]
    field_simp
    simp
    norm_num

    have h_dim :
    (4 * (1 + Real.log 2) + 5 * Real.log 3) 
    ≤ (4 * (1 + Real.log 2) + 5 * Real.log 3) 
    * Module.finrank ℚ (Submodule.span ℚ (insert 1 (Set.range (first_odd_zeta_values 3)))) := by
      apply le_mul_of_one_le_right
      positivity

      norm_cast

      apply Nat.one_le_iff_ne_zero.mpr
      apply Nat.ne_zero_iff_zero_lt.mpr

      have h_finite : Module.Finite ℚ ↥(Submodule.span ℚ (insert (1 : ℝ) (Set.range (first_odd_zeta_values 3)))) := by
        apply Module.Finite.iff_fg.mpr
        apply Submodule.fg_span
        unfold first_odd_zeta_values
        apply Set.Finite.insert
        apply Set.finite_range
      
      rw [Module.finrank_pos_iff]
      
      have h1 : (1 : ℝ) ∈ Submodule.span ℚ (insert 1 (Set.range (first_odd_zeta_values 3))) := by
        apply Submodule.subset_span
        apply Set.mem_insert
      
      apply nontrivial_of_ne ⟨1, h1⟩ 0
      intro h_eq
      injection h_eq with h_val
      exact one_ne_zero h_val


    apply le_trans _ h_dim
    have h1 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : 0 ≤ Real.log 3 := by positivity

    linarith

  · have ha5 : 5 ≤ a := by 
      rcases hodd with ⟨ k, hk ⟩
      omega

    have hyp : hypotheses a (optimal_r a) := {
      hodd_a := hodd
      h3_le_a := h3lea
      h1_le_r := (bounds_on_r a ha5).left
      h2r_le_a := (bounds_on_r a ha5).right
    }

    exact cor_lower_bound_dimension a (optimal_r a) hyp


noncomputable def numerator_of_limit (a: ℕ) : ℝ :=
    ((Real.log (optimal_r a) ) + (a- optimal_r a)/(a+1) * (Real.log 2)) 
    /(Real.log a)

noncomputable def denominator_of_limit (a: ℕ) : ℝ :=
    (1 + (Real.log 2) + ((2 * (optimal_r a) + 1) / (a + 1) ) * (Real.log
    (optimal_r a + 1))) / (1 + Real.log 2)

theorem numerator_tendsto_one : Tendsto numerator_of_limit condFilter (nhds 1) :=
  by sorry

theorem denominator_tendsto_one :
    Tendsto denominator_of_limit condFilter (nhds 1) :=
  by sorry

noncomputable def H (a: ℕ) : ℝ :=
    (second_proposition_bound a (optimal_r a) ) * (1 + Real.log 2)/(Real.log a)

theorem H_is_num_over_denom : H = numerator_of_limit / denominator_of_limit := by
  ext a
  simp only [Pi.div_apply]
  unfold H second_proposition_bound numerator_of_limit denominator_of_limit
  field_simp

theorem lower_bound_and_H (a: ℕ) (ha : 3 ≤ a) :
  numerator_of_limit a / denominator_of_limit a / (1 + Real.log 2) * Real.log a
  = lower_bound_on_optimal_r a := by

  unfold numerator_of_limit denominator_of_limit
  unfold lower_bound_on_optimal_r second_proposition_bound

  have h_log : Real.log a ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    positivity
    norm_cast
    linarith

  have h_log2 : 1 + Real.log 2 ≠ 0 := by
    positivity

  field_simp


theorem limitH : Tendsto H condFilter (nhds 1) := by

  have h1 : (1: ℝ) ≠ 0 := by norm_num
  have g := Filter.Tendsto.div numerator_tendsto_one denominator_tendsto_one h1
  have h2 : ((1: ℝ) / 1)= 1 := by norm_num
  rw [h2] at g
  rw [<- H_is_num_over_denom] at g
  exact g

theorem dimension_asymptotic_bound :
    ∀ ε > 0, ∃ (N : ℕ) , ∀ a ≥ N, (Odd a) → (3 ≤ a) →
    (1-ε)/(1 + (Real.log 2)) * (Real.log a)
    ≤
    dimension_span_first_odd_values_zeta a
    := by

    intro ε hε

    have h := limitH

    have g : ∀ᶠ (x : ℕ) in condFilter, 1 - ε ≤ H x := by
      apply Filter.Tendsto.eventually h
      apply eventually_ge_nhds
      linarith

    rw [condFilter, eventually_inf_principal, eventually_atTop] at g

    rcases g with ⟨N, hN⟩

    use N

    intro a hageN hodd hge3

    have h3 : 1 - ε ≤ H a := by
      tauto

    have h4 := applying_corollary_to_r a hodd hge3

    apply le_trans _ h4

    rw [H_is_num_over_denom, Pi.div_apply] at h3

    calc
    _ ≤ ((numerator_of_limit a) / (denominator_of_limit a)) / (1 + Real.log 2)
    * Real.log a := by gcongr
    _ = lower_bound_on_optimal_r a := by apply lower_bound_and_H a hge3


theorem h_floor : ⌊3 / Real.log 3 ^ 2⌋₊ = 2 := by 
  apply?
