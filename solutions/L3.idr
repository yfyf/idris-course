module Main

data Ty = TyInt | TyBool | TyUnit | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt       = Int
interpTy TyBool      = Bool
interpTy TyUnit      = ()
interpTy (TyFun s t) = interpTy s -> interpTy t

using (G : Vect Ty n)

  data Env : Vect Ty n -> Type where
      Nil  : Env Nil
      (::) : interpTy a -> Env G -> Env (a :: G)

  data HasType : (i : Fin n) -> Vect Ty n -> Ty -> Type where
      stop : HasType fO (t :: G) t
      pop  : HasType k G t -> HasType (fS k) (u :: G) t

  total
  lookup : HasType i G t -> Env G -> interpTy t
  lookup stop    (x :: xs) = x
  lookup (pop k) (x :: xs) = lookup k xs

  total
  update : HasType i G t -> Env G -> interpTy t -> Env G
  update stop (x :: xs) t    = (t :: xs)
  update (pop k) (x :: xs) t = x :: (update k xs t)

  data Expr : Vect Ty n -> Ty -> Type where
       Val : interpTy a -> Expr G a
       Var : HasType i G t -> Expr G t
       Op  : (interpTy a -> interpTy b -> interpTy c) ->
              Expr G a -> Expr G b -> Expr G c
  total
  eval : Env G -> Expr G t -> interpTy t
  eval env (Val a) = a
  eval env (Var v) = lookup v env
  eval env (Op op a b) = op (eval env a) (eval env b)

  infix 5 :=

  data Imp    : Vect Ty n -> Ty -> Type where
       Let    : Expr G t -> Imp (t :: G) u -> Imp G u
       (:=)   : HasType i G t -> Expr G t -> Imp G t
       Print  : Expr G TyInt -> Imp G TyUnit
       For    : Imp G i -> -- initialise
                Imp G TyBool -> -- test
                Imp G x -> -- increment
                Imp G t -> -- body
                Imp G TyUnit
       (>>=)  : Imp G a -> (interpTy a -> Imp G b) -> Imp G b
       Return : Expr G t -> Imp G t

  total
  interp : Env G -> Imp G t -> IO (interpTy t, Env G)
  interp env (Let e b) = let a = eval env e in do
                            (t, _) <- interp (a::env) b
                            return (t, env)
  interp env (v := e) = let val = eval env e in
                            return (val, update v env val)
  interp env (Print e) = let val = eval env e in do
                            putStrLn $ show val
                            return ((), env)
  interp env (For i test inc b) = do
                            (t, env') <- interp env i
                            (bool, env'') <- interp env' test
                            case bool of
                                True => do
                                    (_, env''') <- interp env'' b
                                    interp env''' (For inc test inc b)
                                False =>
                                    return ((), env'')
  interp env (imp >>= m) = do
                            (t, env') <- interp env imp
                            interp env' (m t)
  interp env (Return exp) = let val = eval env exp in
                            return (val, env)


  small : Imp [] TyUnit
  small = Let (Val 42) (do
              Print (Var stop)
              stop := Op (+) (Var stop) (Val 1)
              Print $ Var stop)

-- maybe latter, I don't see how to do it without implicit's
--  small_nice : Imp [] TyUnit
--  small_nice = imp (do
--            let x = 42
--            Print x
--            x := x + 1
--            Print x)
--  count : Imp [] TyUnit
--  count = imp (do
--            let x = 0
--            For (x := 0) (x < 10) (x := x + 1)
--                (Print (x + 1)))


  decent : Imp [] TyUnit
  decent = Let (Val 0) (
            For (stop := (Val 1))
                (Return (Op (<=) (Var stop) (Val 3)))
                (stop := (Op (+) (Var stop) (Val 1)))
                (Print (Var stop)))

  main : IO ()
  main = do
    putStrLn "Small example:"
    interp [] small
    putStrLn "Let's count to 3:"
    interp [] decent
    return ()
