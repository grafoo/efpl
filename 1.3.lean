-- Define the function joinStringsWith with type
-- String -> String -> String -> String that creates a new string by
-- placing its first argument between its second and third arguments.
-- joinStringsWith ", " "one" "and another" should evaluate to "one, and another".

def joinStringsWith (s:String) (x:String) (y:String) : String := String.append x (String.append s y)
def joinStringsWithComma : String -> String -> String := joinStringsWith ", "

#eval joinStringsWith ", " "one" "and another" == "one, and another"
#eval joinStringsWithComma "one" "and another" == "one, and another"

-- What is the type of joinStringsWith ": "? Check your answer with Lean.

#check joinStringsWith ": " -- (String → String → String)


-- Define a function volume with type Nat → Nat → Nat → Nat that computes the
-- volume of a rectangular prism with the given height, width, and depth.

def volume (h:Nat) (w:Nat) (d:Nat) : Nat := h * w * d

#eval volume 2 3 4 == 24
