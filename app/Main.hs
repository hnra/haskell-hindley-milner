module Main where

import HindleyMilner
import Data.HashMap.Strict as HM
import Data.HashSet as HS
import Control.Monad.Trans.State.Strict (evalState)

main :: IO ()
main = do
  let env = envOfList defaultEnv
      subst = HM.fromList [("a", TyLit TyBool)]
      l = TyLambda (TyVar "a") (TyVar "b")
      tyvars = HS.fromList ["a", "b"]
  print $ evalState (envGet "=" env) 0
