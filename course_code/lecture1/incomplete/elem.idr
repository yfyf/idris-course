module elem

import Decidable.Equality

data Elem  : a -> List a -> Type where
     Here  : {xs : List a} -> Elem x (x :: xs)
     There : {xs : List a} -> Elem x xs -> Elem x (y :: xs)

inList : Elem 2 [1..4]
inList = There Here

isElem : (x : Nat) -> (xs : List Nat) -> Maybe (Elem x xs)
