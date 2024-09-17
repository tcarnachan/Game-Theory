import Mathlib

-- Definitions for a two-player game

inductive Player
| One
| Two

abbrev payoff_fun (Strategy : Type) := Player → Strategy → Strategy → Real

def equilibrium (Strategy : Type) (payoff: payoff_fun Strategy) (s1 s2: Strategy) :=
  (∀s1', (payoff Player.One s1' s2) ≤ (payoff Player.One s1 s2)) ∧
    (∀s2', (payoff Player.Two s1 s2') ≤ (payoff Player.Two s1 s2))
