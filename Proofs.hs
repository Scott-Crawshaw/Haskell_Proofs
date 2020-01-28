{-# LANGUAGE NoImplicitPrelude #-} -- disables 'Prelude'
module Proofs where
import Prelude (Eq(..),Show(..),undefined) -- this imports the list datatype definition too

-- we use the following definitions from the prelude:
flip f x y = f y x
const x y = x
id x = x
f . g = \x -> f (g x)

{---------------------------------}
-- Natural numbers with addition --
{---------------------------------}
data Nat = Zero | Suc Nat deriving (Eq,Show)

-- some arithmetics:
add (Suc x) y = Suc (add x y)
add Zero y = y

-- there are some other ways of defining add:
-- we can use an accumulator like this:

add2 (Suc x) y = add x (Suc y)
add2 Zero y = y

-- or we can try and get to zero in either argument as fast as possible
add3 (Suc x) (Suc y) = Suc (Suc (add x y))
add3 Zero y = y
add3 x Zero = x

{---------------------------}
-- some functions on lists --
{---------------------------}

-- we re-define length to produce 'Nat'
length [] = Zero
length (x:xs) = Suc (length xs)

-- our own list operations:
head [] = undefined
head (x:xs) = x

[] ++ ys = ys
(x:xs) ++ ys = x:(xs ++ ys)

reverse [] = []
reverse (x:xs) = reverse xs ++ [x]

foldl f e [] = e
foldl f e (x:xs) = foldl f (f e x) xs

foldr f e [] = e
foldr f e (x:xs) = f x (foldr f e xs)

-- we use the old inefficient version of scanr, but rewritten
scanr f e [] = [e] -- recall that [e] = e:[], you don't need an extra step for this!
scanr f e (x:xs) = f x (foldr f e xs): scanr f e xs

-- We now introduce a datatype for simple mathematical expressions:

data Expr a
 = Const a -- whatever a is, could be a Char to stand for a variable, or an Int, or a Nat
 | Add (Expr a) (Expr a) -- combining two expressions with the 'Add' operator
 deriving (Eq,Show)

-- example: Add (Const 'a') (Const 'b') stands for the expression 'a' + 'b'
-- another example: Add (Const 3) (Add (Const 4) (Const 2)) stands for 3 + (4 + 2)

-- replace the constants, can for instance be used to replace a with 1, b with 2, etc..

replace :: (a -> b) -> Expr a -> Expr b
replace f (Const a) = Const (f a)
replace f (Add x y) = Add (replace f x) (replace f y)

-- evaluate expressions
-- you have to provide it with a function to interpret 'a' or 1 etc as a Nat
evaluate :: (a -> Nat) -> Expr a -> Nat
evaluate f (Const a) = f a
evaluate f (Add x y) = add (evaluate f x) (evaluate f y)

gather :: Expr a -> [a]
gather (Const a) = [a]
gather (Add x y) = gather x ++ gather y

{-

You must prove the following properties:

A. prove that for finite lists xs:
  head (scanr f e xs) = foldr f e xs

B. Assuming the arguments are natural numbers (finite and well-formed),
If you are an undergraduate, prove that: add = add2
If you are a graduate, prove that: add = add3

C. prove for finite lists xs and finite lists ys:
  length (xs ++ ys) = add (length xs) (length ys)

D. prove for finite lists xs:
  reverse xs = foldl (flip (:)) [] xs
Hint:
  You will get stuck using induction, do this first!
  Look at why you cannot apply induction, and invent a stronger property.
  Prove the stronger property using induction instead, and prove the above as a corollary.
  If you can show where you got stuck, you may ask what the stronger property should be.

E. prove that:
  evaluate f (Add x y) = evaluate f (Add y x)
Hint: first prove an auxiliary property about 'add'

F, G, H. assuming the arguments are finite and well-formed expressions:
  evaluate f . replace g = evaluate (f . g)
  length . gather = evaluate (const (Suc Zero))
  foldr add Zero . gather = evaluate id

I. Does the proof you wrote for A apply for arbitrary lists xs?
   What extra cases did you consider and what was the outcome?

J. Give a proof to find out under what conditions does the following holds:
   foldr f e = foldl f e
Your conditions must general enough that you can conclude the following:
   foldr add Zero = foldl add Zero


If you wish to use things from other sources:
- include what you found
- state who's it is, say where you found it


Here is an example proof in Wim Feijen-style:

Assignment prove that: length . scanr f ys = Suc . length

We first prove the property P for finite lists by induction:
P(zs) = (length (scanr f ys zs) = Suc (length zs))
    Base case: zs = []
    P([]) = (length (scanr f ys []) = Suc (length []))
    We show this by computation:
       length (scanr f ys [])
        = {scanr.1}
       length [ys]
        = {length.2}
       Suc (length [])
    This shows P([])
    Inductive case: assume P(zs), we show P(z:zs)
    P(z:zs) = (length f ys (z:zs) = Suc (length (z:zs)))
    We show this by computation:
       length (scanr f ys (z:zs))
        = {scanr.2}
       length (f z (foldr f ys zs): scanr f ys zs)
        = {length.2}
       Suc (length (scanr f ys zs))
        = {induction hypothesis: P(zs)}
       Suc (Suc (length zs))
        = {length.2}
       Suc (length (z:zs))

We now prove the assignment by calculation:
length . scanr f ys
 = {definition of .}
(\xs -> length (scanr f ys xs))
 = {property P (above)}
(\xs -> Suc (length xs))
 = {definition of .}
Suc . length



-}
