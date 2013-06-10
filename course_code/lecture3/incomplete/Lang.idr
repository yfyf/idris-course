module Main

import Effect.State
import Effect.Exception
import Effect.Random
import Effect.StdIO

data Expr = Var String
          | Val Int
          | Add Expr Expr
          | Random Int

Env : Type
Env = List (String, Int)

eval : Expr -> Eff IO [EXCEPTION String, RND, STATE Env] Int

testExpr : Expr
testExpr = Add (Add (Var "foo") (Val 42)) (Random 100)

runEval : List (String, Int) -> Expr -> IO Int

main : IO ()
main = do putStr "Number: "
          x <- getLine
          val <- runEval [("foo", cast x)] testExpr
          putStrLn $ "Answer: " ++ show val


