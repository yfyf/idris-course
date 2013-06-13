module L1

import Decidable.Equality

%default total

--- Exercise 1

total
repeat : (n: Nat) -> a -> Vect a n
repeat O m = []
repeat (S k) m = m :: repeat k m

--- Exercise 2

total
vtake : (n: Nat) -> Vect a (n+m) -> Vect a n
vtake O _ = []
vtake (S k) (x :: xs) = x :: vtake k xs

total
vdrop : (n: Nat) -> Vect a (n+m) -> Vect a m
vdrop O a = a
vdrop (S k) (x :: xs) = vdrop k xs

--- Exercise 3

Matrix : Type -> Nat -> Nat -> Type
Matrix a n m = Vect (Vect a m) n

total
mtrans : Matrix a n m -> Matrix a m n
mtrans [] = repeat _ []
mtrans (r :: rs) = zipWith (::) r (mtrans rs)

total
ptrans : Matrix a (S n) (S m) -> Matrix a (S m) (S n)
ptrans (r :: []) = map (\x => [x]) r
ptrans (r :: (r' :: rs)) = zipWith (::) r (ptrans (r' :: rs))


-- multiplication

total
scalarProd : Vect Nat n -> Vect Nat n -> Nat
scalarProd u v = Vect.foldl (+) O $ zipWith (*) u v

total
mult : Matrix Nat n m -> Matrix Nat m n -> Matrix Nat n n
mult a b = map (\x => map (scalarProd x) $ mtrans b) a

--- Exercise 4

data Cmp : Nat -> Nat -> Type where
     cmpLT : (y : Nat) -> Cmp x (x + S y)
     cmpEQ : Cmp x x
     cmpGT : (x : Nat) -> Cmp (y + S x) y

cmp : (n : Nat) -> (m : Nat) -> Cmp n m
cmp O O = cmpEQ
cmp (S n) O = cmpGT _
cmp O (S m) = cmpLT _
cmp (S n) (S m) with (cmp n m)
  cmp (S i) (S i) | cmpEQ = cmpEQ
  cmp (S i) (S (i + S j)) | cmpLT _ = cmpLT _
  cmp (S (i + S j)) (S j) | cmpGT _ = cmpGT _

--- Exercise 5

total
plus_nSm : (n : Nat) -> (m : Nat) -> n + S m = S (n + m)
plus_nSm O m = refl
plus_nSm (S k) m = ?nSmP1

total
plus_commutes : (n : Nat) -> (m : Nat) -> n + m = m + n
plus_commutes O m = sym (plusZeroRightNeutral m)
plus_commutes (S k) m = let ih = plus_commutes k m in ?comm1

total
plus_assoc : (n : Nat) -> (m : Nat) -> (p : Nat) ->
  n + (m + p) = (n + m) + p
plus_assoc O m p = refl
plus_assoc (S k) m p = let ih = plus_assoc k m p in ?assocP

--- Exercise 6

total
vect_reverse : Vect a n -> Vect a n
vect_reverse [] = []
vect_reverse (x::xs) = revAcc [] (x::xs) where
  revAcc : Vect a i -> Vect a j -> Vect a (i+j)
  revAcc acc [] ?= acc
  revAcc acc (x :: xs) ?= revAcc (x :: acc) xs

--- Exercise 7

data Tree a = Leaf | Node (Tree a) a (Tree a)

using (x:a, ltr: Tree a, rtr: Tree a)
    data ElemTree  : a -> Tree a -> Type where
        ElemHere : ElemTree x (Node ltr x rtr)
        ElemLeft : ElemTree e ltr -> ElemTree e (Node ltr x rtr)
        ElemRight : ElemTree e rtr -> ElemTree e (Node ltr x rtr)

elem_test : ElemTree 3 (Node (Node Leaf 2 Leaf) 1 (Node Leaf 3 Leaf))
elem_test = ElemRight ElemHere

total
elemInTree : DecEq a => (x : a) -> (t : Tree a) -> Maybe (ElemTree x t)
elemInTree x Leaf = Nothing
elemInTree x (Node ltr y rtr) with (decEq x y)
    elemInTree x (Node ltr x rtr) | Yes refl = Just ElemHere
    elemInTree x (Node ltr y rtr) | No _ =
        (fmap ElemLeft $ elemInTree x ltr) <|> (fmap ElemRight $ elemInTree x rtr)

---------- Proofs ----------

L1.revAcc_lemma_2 = proof {
  compute ;
  intros;
  rewrite (plusSuccRightSucc i n1);
  trivial ;
}

L1.revAcc_lemma_1 = proof {
  intros;
  compute ;
  rewrite (plus_commutes O i);
  trivial ;
}

L1.assocP = proof {
  intro k, m, p;
  compute ;
  intros;
  rewrite ih;
  trivial ;
}

L1.comm1 = proof {
  intro k,m;
  compute ;
  intros;
  rewrite  (plusSuccRightSucc m k);
  rewrite ih;
  trivial ;
}

L1.nSmP1 = proof {
  intros;
  let ih = plus_nSm k m;
  compute;
  rewrite ih;
  trivial ;
}

