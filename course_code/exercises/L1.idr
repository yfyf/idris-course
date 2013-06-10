module L1

import Decidable.Equality

-- vtake, vdrop, types and implementations missing

Matrix : Type -> Nat -> Nat -> Type
Matrix a n m = Vect (Vect a m) n

data Cmp : Nat -> Nat -> Type where
     cmpLT : (y : _) -> Cmp x (x + S y)
     cmpEQ : Cmp x x
     cmpGT : (x : _) -> Cmp (y + S x) y

cmp : (n : Nat) -> (m : Nat) -> Cmp n m
-- implementation missing

plus_nSm : (n : Nat) -> (m : Nat) -> n + S m = S (n + m)
-- implementation missing

plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
-- implementation missing

plus_assoc : (n : Nat) -> (m : Nat) -> (p : Nat) ->
             n + (m + p) = (n + m) + p
-- implementation missing

vect_reverse : Vect a n -> Vect a n
-- implementation missing

data Tree a = Leaf | Node (Tree a) a (Tree a)

data ElemTree  : a -> Tree a -> Type where 
     {} -- constructors

elemInTree : DecEq a => (x : a) -> (t : Tree a) -> Maybe (ElemTree x t)
-- implementation missing

