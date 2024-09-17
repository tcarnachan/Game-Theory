-- import Mathlib.Tactic

inductive Game
| ending : Game -- Ending Game
| options : List Game → Game -- Game options

def game_lt (g1 g2: Game) : Prop :=
match g1, g2 with
| Game.ending, _ => False
| _, Game.ending => True
| Game.options l1, _ => l1.contains g2

instance : LT Game where
  lt := game_lt

def game_sum (g1 g2: Game) : Game :=
match g1, g2 with
| Game.ending, _ => g2
| _, Game.ending => g1
| Game.options l1, Game.options l2 =>
  Game.options (List.map (λg => game_sum g g2) l1 ++ List.map (λg => game_sum g1 g) l2)
