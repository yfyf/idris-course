module Main

import Effect.State
import Effect.Exception
import Effect.Random
import Effect.StdIO

data Ty = TyInt | TyBool | TyString | TyUnit | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt       = Int
interpTy TyBool      = Bool
interpTy TyString    = String
interpTy TyUnit      = ()
interpTy (TyFun s t) = interpTy s -> interpTy t

data Environment : Effect where
    GetEnv : String -> Environment () () String
    GetArgs : Environment () () (List String)

instance Handler Environment IO where
    handle () (GetEnv s) k = do x <- System.getEnv s; k () x
    handle () GetArgs k = do x <- System.getArgs; k () x

ENVIRONMENT : EFFECT
ENVIRONMENT = MkEff () Environment

getEnv : Handler Environment e => String -> Eff e [ENVIRONMENT] String
getEnv s = GetEnv s

getArgs : Handler Environment e => Eff e [ENVIRONMENT] (List String)
getArgs = GetArgs

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

  data Vars = EffState | EffState2 | EffIO

  --total
  eval : Expr G t -> Eff IO [STATE (Env G), ENVIRONMENT] (interpTy t)
  eval (Val a) = return a
  eval (Var v) = do env <- get
                    Effects.return $ lookup v env
  eval (Op op a b) = do
                        a' <- eval a
                        b' <- eval b
                        return (op a' b')

  infix 5 :=

  data Imp    : Vect Ty n -> Ty -> Type where
       Let    : Expr G t -> Imp (t :: G) u -> Imp G u
       (:=)   : HasType i G t -> Expr G t -> Imp G t
       Print  : Expr G TyInt -> Imp G TyUnit
       -- how to get rid of this?
       PrintS  :Imp G TyString -> Imp G TyUnit
       GetSysEnv : Expr G TyString -> Imp G TyString
       GetSysArgs : Imp G TyString
       For    : Imp G i -> -- initialise
                Imp G TyBool -> -- test
                Imp G x -> -- increment
                Imp G t -> -- body
                Imp G TyUnit
       (>>=)  : Imp G a -> (interpTy a -> Imp G b) -> Imp G b
       Return : Expr G t -> Imp G t


  --total
  interp : Imp G t -> Eff IO [STATE (Env G), STDIO, ENVIRONMENT] (interpTy t)
  interp (Print e) = do val <- eval e
                        putStrLn (show val)
  -- how to get rid of this?
  interp (PrintS e) = do
                        val <- interp e
                        putStrLn (show val)
  interp (GetSysEnv s) = do s' <- eval s
                            e <- Main.getEnv s'
                            return e
  interp GetSysArgs = do
                        e <- Main.getArgs
                        return (show e)
  interp (v := e) = do val <- eval e
                       State.update (\env => Main.update v env val)
                       return val
  interp (Let e b) = do a <- eval e
                        -- @TODO: why doesn't updateM work here?
                        -- updateM ((::) a)
                        env <- get
                        putM (a :: env)
                        val <- interp b
                        -- @TODO: same here
                        -- updateM tail
                        (_ :: env') <- get
                        putM env'
                        return val
  interp (imp >>= m) = do t <- interp imp
                          interp (m t)
  interp (Return exp) = eval exp
  interp (For i test inc b) = do
                            t <- interp i
                            bool <- interp test
                            if bool then do
                                        interp b
                                        interp (For inc test inc b)
                                else return ()

  small : Imp [] TyUnit
  small = Let (Val 42) (do
              Print (Var stop)
              stop := Op (+) (Var stop) (Val 1)
              Print $ Var stop)

  decent : Imp [] TyUnit
  decent = Let (Val 0) (
            For (stop := (Val 1))
                (Return (Op (<=) (Var stop) (Val 3)))
                (stop := (Op (+) (Var stop) (Val 1)))
                (Print (Var stop)))

  getTerm : Imp [] TyUnit
  getTerm = (PrintS (GetSysEnv (Val "TERM")))

  getSysArgs : Imp [] TyUnit
  getSysArgs = PrintS GetSysArgs

  main : IO ()
  main = do
    putStrLn "Small example:"
    run [Main.Nil, (), ()] (interp small)
    putStrLn "Let's count to 3:"
    run [Main.Nil, (), ()] (interp decent)
    putStr "What's my TERM? "
    run [Main.Nil, (), ()] (interp getTerm)
    putStrLn "What args did I use? "
    run [Main.Nil, (), ()] (interp getSysArgs)
    return ()
