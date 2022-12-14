{-# LANGUAGE StrictData #-}

module HindleyMilner where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Control.Monad.Trans.State.Strict (State, get, put, evalState)

data TyLit = TyInt | TyBool | TyStr
    deriving Eq

instance Show TyLit where
    show TyInt = "Int"
    show TyBool = "Bool"
    show TyStr = "String"

data Ty = TyVar String | TyLit TyLit | TyLambda Ty Ty

instance Show Ty where
    show (TyVar v) = v
    show (TyLit lit) = show lit
    show (TyLambda from to) = "(" ++ show from ++ " -> " ++ show to ++ ")"

data Lit = LitInt Int | LitBool Bool | LitStr String
    deriving Show

data Expr =
      Lit Lit
    | Var String
    | Let String Expr Expr
    | Lambda String Expr
    | App Expr Expr
    deriving Show

type StringMap = HashMap String

-- | A substitution is mapping from a type variable to a type.
type Subst = StringMap Ty

-- | Inserts a type variable constraint. E.g. may constrain the type 't1' to Int.
makeConstraint :: String -> Ty -> Subst -> Subst
makeConstraint = HM.insert

-- | Applies substitutions to all type variables within the type.
refineType :: Subst -> Ty -> Ty
refineType s t@(TyVar v) = HM.findWithDefault t v s
refineType s (TyLambda a b) = TyLambda (refineType s a) (refineType s b)
refineType s t@(TyLit _) = t

type StringSet = HashSet String

-- | Retrieves the set of type variables of the type.
tyvarsFromType :: Ty -> StringSet
tyvarsFromType (TyVar v) = HS.singleton v
tyvarsFromType (TyLambda a b) = HS.union (tyvarsFromType a) (tyvarsFromType b)
tyvarsFromType (TyLit _) = HS.empty

-- | An environment is mapping from a symbol to its type and unbound type variables.
type Env = StringMap (Ty, StringSet)

-- |┬áRetrieves the set of type variables which occurr in the environment.
tyvarsFromEnv :: Env -> StringSet
tyvarsFromEnv =
    HM.foldr (
        \(t, tvars) acc ->
            HS.union
                ( HS.difference (tyvarsFromType t) tvars )
                  acc
                )
    HS.empty

-- | Adds a mapping from a symbol to a type and a set of type variables.
envAdd :: String -> (Ty, StringSet) -> Env -> Env
envAdd = HM.insert

-- | Create an unused type variable.
makeNewType :: State Int Ty
makeNewType = do
    i <- get
    put (i + 1)
    return $ TyVar ("t" ++ show i)

-- | Instantiates a type by giving its type variables unique identifiers.
-- E.g. in the type (a -> a) 'a' does not refer to a unique type named
-- a but any type possible. We use the state monad to generate a unique
-- type variable, e.g. 't0' instead, so the type becomes t0 -> t0.
-- Question: Is this robust? Can we create a variable or something which
-- leads to problems? The typing haskell in haskell paper did something similar.
instantiateType :: Ty -> StringSet -> State Int Ty
instantiateType t tvars = do
    i <- get
    let
        aggregate v ssubs = do
            subs <- ssubs
            nt <- makeNewType
            return $ HM.insert v nt subs
        emptyMap = put i >> pure HM.empty
        subs' = HS.foldr aggregate emptyMap tvars
    subs <- subs'
    return $ refineType subs t

-- | Gets the type bound by the symbol.
envGet :: String -> Env -> State Int Ty
envGet v e = case HM.lookup v e of
    Just (t, tvars) -> instantiateType t tvars
    Nothing -> error $ "Unbound variable: " ++ show v

-- | Refines the environment by applying all subsitutions.
-- E.g. we may have found that the expression 'four' has type
-- 'Int'. This function will substitute all occurrences of 'four'
-- in any other expression with 'Int'.
refineEnv :: Subst -> Env -> Env
refineEnv s = HM.map refineEntry
    where
        -- | Refines the type 't'.
        refineEntry (t, v) =
            (refineType 
                -- Why are we removing all substitutions of type variables?
                -- Because these variables are unbound by definition?
                -- Avoiding some sort of collision?
                ( HS.foldr HM.delete s v ) 
                t, v)

-- | Unifies two types using the available substitutions by adding
-- the subsitutions which unify them.
unify :: Ty -> Ty -> Subst -> Subst
unify t1 t2 s =
    case (t1', t2') of
        -- Two type variables unify if they are the same.
        ab@(TyVar v1, TyVar v2) ->
            if v1 == v2 then s else uncurry failUnify ab

        -- We can always unify a type variable with a non type variable if
        -- no cycles occurr. Consider the substitution a: b -> a. Trying to
        -- refine using this substitution would create an infinite loop, so
        -- we must make sure (here) that we do not create any such substitutions.
        ab@(TyVar v1, b) ->
            if noCycle v1 t2 then makeConstraint v1 t2' s else uncurry failUnify ab

        -- Flip and unify.
        (_, TyVar v2) -> unify t2' t1' s

        -- Unifies two lamda by unifying their argument and their return.
        (TyLambda from1 to1, TyLambda from2 to2) ->
            unify from1 from2 (unify to1 to2 s)

        -- Two literals unify if they are the same type.
        (TyLit l1, TyLit l2) -> if l1 == l2 then s else failUnify l1 l2

        (a, b) -> failUnify a b
    where
        t1' = refineType s t1
        t2' = refineType s t2
        noCycle v t = not (HS.member v (tyvarsFromType t))
        failUnify t1' t2' = error $ "Cannot unify " ++ show (t1', t2')

litToType :: Lit -> TyLit
litToType (LitInt _) = TyInt
litToType (LitBool _) = TyBool
litToType (LitStr _) = TyStr

-- | Retrieves the set of type variables of 't' not bound by the environment.
generalize :: Env -> Ty -> (Ty, StringSet)
generalize e t = (t, d)
    where
        tvars = tyvarsFromType t
        etvars = tyvarsFromEnv e
        d = HS.difference tvars etvars

-- | The meat and potatoes of the type inference.
--
-- Inspects the expression 'expr' with regards to the current
-- environment and a mapping of substitutions by trying to unify
-- the expression with a type 'ty'. The result is an extended mapping
-- of substitutions which can be used to refine the type 'ty'.
--
-- This is the function which actually binds the programming language
-- and the type system together. By inspecting an expression together
-- with a type variable we can then inspect that type variable using
-- the resulting list of substitutions to find out its type.
inspectExpr :: Env -> Expr -> Ty -> Subst -> State Int Subst
inspectExpr env expr ty subs =
    case expr of
        -- If the expression is a literal try to unify its type with 'ty'.
        -- For the simple case where 'ty' is a type variable this simply
        -- adds a substitution of 'ty' with the type of literal.

        -- If 'ty' is the type of a literal then this verifies that the
        -- expression type and 'ty' does indeed match.
        Lit l -> return $ unify ty (TyLit (litToType l)) subs

        -- If the expression is a variable then we retrieve its bound
        -- type from the environment, refine it using the supplied substitutions,
        -- and then try to unify it with 'ty'.
        --
        -- Note that retrieving an unbound variable is an error. So any variable
        -- we typecheck needs to bound by the environment. This binding is either
        -- done via an enclosing 'let' expression or by structuring the typechecking
        -- in such a way that this is not a problem.
        -- Question: Is this done via a dependency graph? By assigning it a type variable?
        Var v -> do
            nt <- envGet v env
            let t = refineType subs nt
            return $ unify ty t subs

        Let v e1 e2 -> do
            e1Ty <- makeNewType
            subs' <- inspectExpr env e1 e1Ty subs
            let e1Ty' = refineType subs' e1Ty
                scheme = generalize (refineEnv subs' env) e1Ty'
                env' = envAdd v scheme env
            inspectExpr (refineEnv subs' env') e2 ty subs'

        Lambda v e ->do
            vt <- makeNewType
            et <- makeNewType
            let newSubs = unify ty (TyLambda vt et) subs
                newEnv = envAdd v (vt, HS.empty) env
            inspectExpr newEnv e et newSubs

        App f e ->do
            et <- makeNewType
            let ft = TyLambda et ty
            eSubs <- inspectExpr env e et subs
            let ft' = refineType eSubs ft
            inspectExpr (refineEnv eSubs env) f ft' eSubs

defaultEnv :: [(String, Ty)]
defaultEnv =
    [ ("+", TyLambda (TyLit TyInt) (TyLambda (TyLit TyInt) (TyLit TyInt)))
    , ("-", TyLambda (TyLit TyInt) (TyLambda (TyLit TyInt) (TyLit TyInt)))
    , ("^", TyLambda (TyLit TyStr) (TyLambda (TyLit TyStr) (TyLit TyStr)))
    , ("=", TyLambda (TyVar "a") (TyLambda (TyVar "a") (TyLit TyBool)))
    , ("/=", TyLambda (TyVar "a") (TyLambda (TyVar "a") (TyLit TyBool)))
    , ("not", TyLambda (TyLit TyBool) (TyLit TyBool))
    ]

envOfList :: [(String, Ty)] -> Env
envOfList = foldl (\e (v, t) -> envAdd v (generalize e t) e) HM.empty

-- | Retrieves the type of an expression.
typeOf :: Expr -> Ty
typeOf e = flip evalState 0 $ do
    let
        env = envOfList defaultEnv
        emptySubs = HM.empty
    et <- makeNewType
    subs <- inspectExpr env e et emptySubs
    return $ refineType subs et
