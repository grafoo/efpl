-- Define a structure named RectangularPrism that contains the height, width, and depth
-- of a rectangular prism, each as a Float.

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float
deriving Repr


-- Define a function named volume : RectangularPrism → Float that computes the volume of
-- a rectangular prism.

def volume (rp:RectangularPrism) : Float := rp.depth * rp.height * rp.width


-- Define a structure named Segment that represents a line segment by its endpoints, and
-- define a function length : Segment → Float that computes the length of a line segment.
-- Segment should have at most two fields.

structure Segment where
  point_a : Float
  point_b : Float
deriving Repr

def length (s:Segment) : Float := ((s.point_a-s.point_b)^2)^(1/2)

#eval length (Segment.mk (-1) 4)
#eval length (Segment.mk (2.75) 8.25)


-- Which names are introduced by the declaration of RectangularPrism?

-- Answer: RectangularPrism.{mk,height,width,depth}


-- Which names are introduced by the following declarations of Hamster and Book?
-- What are their types?

structure Hamster where
  name : String
  fluffy : Bool

-- Answer:
-- Hamster.mk : (name:String) → (fluffy:Bool) -> Hamster
-- Hamster.name : String
-- Hamster.fluffy : Bool

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

-- Answer:
-- Book.makeBook : (title:String) → (author:String) → (price:Float) → Book
-- Book.title : String
-- Book.author : String
-- Book.price : Float
