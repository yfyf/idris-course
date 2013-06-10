module plus_theorem

plus_nO : (n : Nat) -> n + O = n
plus_nO O     = ?pnO_Ocase
plus_nO (S k) = let indH = plus_nO k in ?pnO_Scase

---------- Proofs ----------

plus_theorem.pnO_Scase = proof {
  compute;
  intros;
  rewrite indH;
  trivial;
}

plus_theorem.pnO_Ocase = proof {
  compute;
  trivial;
}

