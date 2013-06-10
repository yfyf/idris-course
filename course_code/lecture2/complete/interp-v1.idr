module Main

data Ty = TyInt | TyBool | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt       = Int
interpTy TyBool      = Bool
interpTy (TyFun s t) = interpTy s -> interpTy t





















-----

using (n : Nat, G : Vect Ty n)

  data Env : Vect Ty n -> Type where
      Nil  : Env Nil
      (::) : interpTy a -> Env G -> Env (a :: G)

  data HasType : (i : Fin n) -> Vect Ty n -> Ty -> Type where
      stop : HasType fO (t :: G) t
      pop  : HasType k G t -> HasType (fS k) (u :: G) t

  lookup : HasType i G t -> Env G -> interpTy t
  lookup stop    (x :: xs) = x
  lookup (pop k) (x :: xs) = lookup k xs

------

  data Expr : Vect Ty n -> Ty -> Type where
      Var : HasType i G t -> Expr G t
      Val : (x : Int) -> Expr G TyInt
      Lam : Expr (a :: G) t -> Expr G (TyFun a t)
      App : Expr G (TyFun a t) -> Expr G a -> Expr G t
      Op  : (interpTy a -> interpTy b -> interpTy c) -> 
            Expr G a -> Expr G b -> Expr G c
      If  : Expr G TyBool -> Expr G a -> Expr G a -> Expr G a
 
------
  
  interp : Env G -> Expr G t -> interpTy t
  interp env (Var i)     = lookup i env
  interp env (Val x)     = x
  interp env (Lam sc)    = \x => interp (x :: env) sc
  interp env (App f s)   = (interp env f) (interp env s)
  interp env (Op op x y) = op (interp env x) (interp env y)
  interp env (If x t e)  = if interp env x then interp env t 
                                           else interp env e



















------

  eId : Expr G (TyFun TyInt TyInt)
  eId = Lam (Var stop)

  eAdd : Expr G (TyFun TyInt (TyFun TyInt TyInt))
  eAdd = Lam (Lam (Op (+) (Var (pop stop)) (Var stop)))
  
  eDouble : Expr G (TyFun TyInt TyInt)
  eDouble = Lam (App (App eAdd (Var stop)) (Var stop))

  (<$>) : |(fun:Expr G (TyFun s t)) -> |(arg : Expr G s) -> Expr G t
  (<$>) = App

  fact : Expr G (TyFun TyInt TyInt)
  fact = Lam (If (Op (==) (Var stop) (Val 0))
                 (Val 1)
                 (Op (*) (fact <$> (Op (-) (Var stop) (Val 1))) (Var stop)))

testFac : Int
testFac = interp [] fact 4

unitTestFac : so (interp [] fact 4 == 24)
unitTestFac = oh

main : IO ()
main = print testFac

