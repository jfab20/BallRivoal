import Mathlib
import BallRivoal.definitions

open Polynomial
open Filter Topology
open Complex
open Asymptotics

variable (a : ℕ)

theorem dimension_at_least_log_over_3 (hodd_a: Odd a) (h3_le_a: 3 ≤ a) :
    1/3 * (Real.log a) ≤
    dimension_span_first_odd_values_zeta a :=
  by
  sorry
