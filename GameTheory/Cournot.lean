import GameTheory.TPDefs

-- Finite Cournot, players are limited to 4 strategies
inductive FiniteStrat
| Zero
| Three
| Four
| Six

def finiteNat : FiniteStrat → Nat
| FiniteStrat.Zero => 0
| FiniteStrat.Three => 3
| FiniteStrat.Four => 4
| FiniteStrat.Six => 6

def finite_cournot_payoff (p: Player) (s1 s2: FiniteStrat) : Real :=
have (v1, v2) := (finiteNat s1, finiteNat s2)
match p with
| Player.One => v1 * (12 - v1 - v2)
| Player.Two => v2 * (12 - v1 - v2)

theorem finite_cournot_equi_is_four
  : equilibrium FiniteStrat finite_cournot_payoff FiniteStrat.Four FiniteStrat.Four
:= by
  rw [equilibrium]
  constructor
  all_goals {
    intro s
    repeat rw [finite_cournot_payoff, finiteNat]
    norm_num
    cases s with
    | _ =>
      repeat rw [finiteNat]
      norm_num
  }

-- The infinite version

def cournot_payoff (p: Player) (s1 s2: Real) : Real :=
match p with
| Player.One => s1 * (12 - s1 - s2)
| Player.Two => s2 * (12 - s1 - s2)

theorem ineq : ∀(x: Real), x * 8 - x ^ 2 ≤ 16 ↔ (x - 4)^2 ≥ 0 := by
  sorry

theorem cournot_equi_is_four : equilibrium Real cournot_payoff 4 4 := by
rw [equilibrium]
constructor
all_goals {
  intro s
  repeat rw [cournot_payoff]
  ring_nf
  rw [ineq]
  exact sq_nonneg (s - 4)
}
