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

  lookup : HasType i G t -> Env G -> interpTy t
  lookup stop    (x :: xs) = x
  lookup (pop k) (x :: xs) = lookup k xs

  update : HasType i G t -> Env G -> interpTy t -> Env G
  -- implementation missing

  data Expr : Vect Ty n -> Ty -> Type where
       Val : interpTy a -> Expr G a
       Var : HasType i G t -> Expr G t
       Op  : (interpTy a -> interpTy b -> interpTy c) ->
              Expr G a -> Expr G b -> Expr G c

  eval : Env G -> Expr G t -> interpTy t
  -- implementation missing

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
    
  interp : Env G -> Imp G t -> IO (interpTy t, Env G)
  -- implementation missing

  small : Imp [] TyUnit
  small = Let (Val 42) (do Print (Var stop)
                           stop := Op (+) (Var stop) (Val 1)
                           Print (Var stop))

  main : IO ()
  main = do interp [] small; return ()
