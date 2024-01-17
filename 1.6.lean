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

inductive PetName (α:Type) (β:Type) : Type where
  | dog : α → PetName α β
  | cat : β → PetName α β
deriving Repr

def pets :=
  [PetName.dog "Spot", PetName.cat "Tiger", PetName.dog "Fifi", PetName.dog "Rex", PetName.cat "Floof"]

def howManyDogs (pets : List (PetName String String)) : Nat := match pets with
  | [] => 0
  | PetName.dog _ :: pets' => howManyDogs pets' + 1
  | PetName.cat _ :: pets' => howManyDogs pets'

#eval howManyDogs pets == 3


-- Write a function zip that combines two lists into a list of pairs.
-- The resulting list should be as long as the shortest input list.
-- Start the definition with def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=.

def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  if List.length xs <= List.length ys
  then match xs with
  | [] => []
  | x :: xs' => match ys with
    | [] => []
    | y::ys' =>(x, y) :: (zip xs' ys')
  else match ys with
  | [] => []
  | y :: ys' => match xs with
    | []=>[]
    | x::xs' => (x, y) :: (zip  xs' ys')

#eval zip [1,3,5] [2,4,6]
#eval zip [1,3] [2,4,6]
#eval zip [1,3,5] [2,4]

-- Write a polymorphic function take that returns the first n entries in a list, where n is a Nat.
-- If the list contains fewer than n entries, then the resulting list should be the input list.
-- #eval take 3 ["bolete", "oyster"] should yield ["bolete", "oyster"], and
-- #eval take 1 ["bolete", "oyster"] should yield ["bolete"].

-- TODO: Use implicit argument?

def take (α : Type) (n : Nat) (xs : List α  ) : List α :=
  if n >= List.length xs
  then xs
  else if n == 0 then [] else match xs with
  | [] => []
  | x :: xs' => x :: take α (n-1) xs'

#eval take String 3 ["bolete", "oyster"] == ["bolete", "oyster"]
#eval take String 1 ["bolete", "oyster"] == ["bolete"]


-- Using the analogy between types and arithmetic, write a function that distributes products over sums.
-- In other words, it should have type α × (β ⊕ γ) → (α × β) ⊕ (α × γ).

def dist (α:Type) (β:Type ) (γ:Type ) (x:α × (β ⊕ γ)) : (α × β) ⊕ (α × γ):=
  match Prod.snd x with
  | Sum.inl y =>Sum.inl (Prod.fst x, y)
  | Sum.inr y=>Sum.inr (Prod.fst x,y)

#check dist

-- Using the analogy between types and arithmetic, write a function that turns multiplication by
-- two into a sum. In other words, it should have type Bool × α → α ⊕ α.

-- TODO: Bool?
