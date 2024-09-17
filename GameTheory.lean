-- This module serves as the root of the `GameTheory` library.
-- Import modules here that should be built as part of the library.
import GameTheory.Defs

open Std

def single_pile_game (n: Nat) : Game :=
  let m  := HashMap.empty
  let m := m.insert n 1
  m

theorem single_pile_is_winning: ∀n: Nat, n > 0 → winning_game (single_pile_game n) := by
  intro n
  intro x
  rw [winning_game]
  use (n, n)
  rw [valid_move, single_pile_game]
  simp
  rw [losing_pos, apply_move]
  simp
  intro k
  induction n with
  | zero => trivial
  | succ Nat.zero => sorry
  | succ n => induction k with
    | zero => simp
    | succ n =>
      sorry
  constructor
  . induction n with
    | zero => trivial
    | succ n =>
      rw [losing_pos, single_pile_game]
      simp
      use (n + 1)
      simp
  . use n
    rw [single_pile_game, valid_move]
    simp
