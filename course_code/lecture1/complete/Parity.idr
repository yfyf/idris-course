module Parity

data Parity : Nat -> Type where
   even : Parity (n + n)
   odd  : Parity (S (n + n))

parity : (n:Nat) -> Parity n
parity O     = even {n = O}
parity (S O) = odd {n = O}
parity (S (S k)) with (parity k)
    parity (S (S (j + j)))     | even ?= even {n=S j}
    parity (S (S (S (j + j)))) | odd  ?= odd {n=S j}


---------- Proofs ----------

Parity.parity_lemma_1 = proof {
  compute;
  intros;
  rewrite sym (plusSuccRightSucc j j);
  trivial;
}

Parity.parity_lemma_2 = proof {
  compute;
  intros;
  rewrite sym (plusSuccRightSucc j j);
  trivial;
}

