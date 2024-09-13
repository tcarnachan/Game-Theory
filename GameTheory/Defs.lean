import «GameTheory».Utils
open Std

-- Size of pile (number of tokens) -> Number of piles of that size
abbrev Game := HashMap Nat Nat

-- Check if two games are equal
def game_equal (g1: Game) (g2: Game) : Bool :=
  _equal (keys_union g1 g2)
where
  _equal (l: List Nat) : Bool :=
  match l with
  | List.nil => True -- Both completed games
  | List.cons h t => (h = 0 ∨ (op_equal g1[h]? g2[h]?)) ∧ _equal t

-- Check if g2 is an option of g1
def is_option (g1: Game) (g2: Game) : Bool :=
  have diffs := get_diffs (keys_union g1 g2)
  -- If a pile of size P was removed, we should have [(P, x, x - 1)]
  -- If a pile of size P was was reduced by p < P,
  --   we should have [(P, x, x - 1), (P - p, y - 1, y)]
  match diffs with
  | List.nil => False -- No change
  | List.cons h List.nil => -- One pile was removed
    have (x, y) := h.snd
    x = Nat.succ y
  | List.cons h1 (List.cons h2 List.nil) => -- One pile was reduced
    have (p1, p2) := (h1.fst, h2.fst)
    have (x1, y1) := h1.snd
    have (x2, y2) := h2.snd
    p1 > p2 ∧ x1 = Nat.succ y1 ∧ Nat.succ x2 = y2
  | _ => False -- More than one pile was changed
where
  -- Gets the differences between g1 and g2 in the form [(key, g1 value, g2 value)]
  get_diffs (l: List Nat) : List (Nat × Nat × Nat) :=
  match l with
  | List.nil => []
  | List.cons h t =>
    have l1 := get_diffs t
    -- Ignore the piles of size 0
    if h = 0 then l1 else
      have (gh1, gh2) := (g1[h]?.getD 0, g2[h]?.getD 0)
      if op_equal gh1 gh2 then l1 else List.cons (h, gh1, gh2) l1

-- Check if a game has been won (no piles left)
def is_won (g: Game) := game_equal g HashMap.empty

-- It will terminate because the option is always 'smaller' than the game
partial def winning_game (g: Game) :=
  if is_won g then False
  else ∃g', is_option g g' ∧ (is_won g' ∨ ∃g'', is_option g' g'' ∧ winning_game g'')

def temp: Game :=
  let m := HashMap.empty
  let m := m.insert 5 2
  m

-- theorem temp_is_winning : winning_game temp :=

-- end


-- unsafe def losing_game (g: Game) :=
--   ∀g', is_option g g' → winning_game g'

def game_sum (g1: Game) (g2: Game) : Game :=
  _sum (keys_union g1 g2)
where
  _sum (l: List Nat) : HashMap Nat Nat :=
  match l with
  | List.nil => HashMap.empty
  | List.cons h t =>
    have m := _sum t
    let m := m.insert h (g1[h]?.getD 0 + g2[h]?.getD 0)
    m

-- Ignore below, temporary stuff for debugging
def temp1: Game :=
  let m := HashMap.empty
  let m := m.insert 0 99
  let m := m.insert 5 2
  m

def temp2: Game :=
  let m := HashMap.empty
  let m := m.insert 5 2
  let m := m.insert 0 23
  m

#eval game_equal temp1 temp2

def temp3: Game :=
  let m := HashMap.empty
  let m := m.insert 3 1
  let m := m.insert 2 1
  let m := m.insert 1 1
  m

def temp4: Game :=
  let m := HashMap.empty
  let m := m.insert 1 2
  let m := m.insert 2 1
  m

#eval is_option temp3 temp4

#eval game_sum temp1 temp2
#eval game_sum temp3 temp4
#eval game_sum temp1 temp4

def temp5: Game :=
  let m := HashMap.empty
  let m := m.insert 1 1
  m

-- example :=
  -- winning_game temp5

-- example : ∃g, winning_game g := by
  -- exact

-- #print winning_game

-- inductive Game where
-- | Single (tokens: Nat) : Game
-- | Sum (lhs: Game) (rhs: Game) : Game

-- def equal (g1: Game) (g2: Game) : Prop :=
-- match g1, g2 with
-- | Game.Single tk1, Game.Single tk2 => tk1 = tk2
-- | Game.Sum g1 p1, Game.Sum g2 p2 => equal g1 g2 ∧ p1 = p2
-- | _, _ => False

-- def is_option (g1: Game) (g2: Game) : Prop :=
-- match g1, g2 with
-- | Game.Single 0, _ => False -- Game is already over, no more moves
-- | Game.Sum (Game.Single 0) _, Game.Empty => True -- Remove last pile
-- | Game.Sum g1 p1, Game.Sum g2 p2 => (equal g1 g2 ∧ p1 > p2)
--   ∨ (p1 = p2 ∧ is_option g1 g2)
-- | _, _ => False -- g2 is empty
