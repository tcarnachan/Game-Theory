import Std.Data.HashMap
open Std

-- Check if two Option Nats are equal, taking 0 equal to none
def op_equal (o1: Option Nat) (o2: Option Nat) : Bool :=
  (o1.getD 0) = (o2.getD 0)

-- Set-like union of two hashmaps' keys
def keys_union {α β: Type} [BEq α] [Hashable α]
                (l1: HashMap α β) (l2: HashMap α β) : List α :=
  (l1.keys ++ l2.keys).eraseDups
