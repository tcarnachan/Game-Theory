import Mathlib.Tactic

import GameTheory.TPDefs

inductive Strat
| Coop
| Defect

def _payoff : Strat × Strat → Real
  | (Strat.Coop, Strat.Coop) => -1
  | (Strat.Defect, Strat.Defect) => 0
  | (Strat.Coop, Strat.Defect) => -10
  | _ => -5

def payoff (p: Player) (s1 s2: Strat) : Real :=
  match p with
  | Player.One => _payoff (s1, s2)
  | Player.Two => _payoff (s2, s1)

-- structure Game with
--   players : Player
--   strats: Player → Strat
--   payoff: Player → Strat → Strat → Nat

theorem defect_defect_is_equilibrium:
equilibrium Strat payoff Strat.Defect Strat.Defect := by
  constructor
  all_goals {
    intro s
    cases s
    repeat simp [payoff, _payoff]
  }
