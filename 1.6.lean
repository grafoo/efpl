-- Write a function to find the last entry in a list.
-- It should return an Option.

def lastEntry {α : Type} (xs : List α) : Option α := match xs with
  | [] => none
  | last :: [] => some last
  | _ :: rest => lastEntry rest

#eval lastEntry [1, 2, 3] == some 3
#eval lastEntry [] (α := Int) == none


-- Write a function that finds the first entry in a list that satisfies a
-- given predicate. Start the definition with
-- def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | head :: tail => if predicate head
      then some head
      else List.findFirst? tail predicate

def gt2 (x:Nat) : Bool := x > 2

#eval [1, 2, 3, 4].findFirst? gt2 == some 3


-- Write a function Prod.swap that swaps the two fields in a pair.
-- Start the definition with def Prod.swap {α β : Type} (pair : α × β) : β × α :=

def Prod.swap {α β : Type} (pair : α × β) : β × α := match pair with
  | (fst, snd) => (snd, fst)

#eval (1, 2).swap == (2, 1)


-- Rewrite the PetName example to use a custom datatype and compare it to the version that uses Sum.


-- Write a function zip that combines two lists into a list of pairs.
-- The resulting list should be as long as the shortest input list.
-- Start the definition with def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=.


-- Write a polymorphic function take that returns the first n entries in a list, where n is a Nat.
-- If the list contains fewer than n entries, then the resulting list should be the input list.
-- #eval take 3 ["bolete", "oyster"] should yield ["bolete", "oyster"], and
-- #eval take 1 ["bolete", "oyster"] should yield ["bolete"].


-- Using the analogy between types and arithmetic, write a function that distributes products over sums.
-- In other words, it should have type α × (β ⊕ γ) → (α × β) ⊕ (α × γ).


-- Using the analogy between types and arithmetic, write a function that turns multiplication by
-- two into a sum. In other words, it should have type Bool × α → α ⊕ α.
