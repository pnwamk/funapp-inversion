{-# LANGUAGE GADTs, StandaloneDeriving #-}
module Types.LazyBDD
  ( Ty(..)
  , Env(..)
  , BDD(..)
  , Arrow(..)
  , Prod(..)
  , extend
  , resolve
  , prodTy
  , arrowTy
  , parseTy
  , tyAnd
  , tyAnd'
  , tyOr
  , tyOr'
  , tyDiff
  , tyNot
  , emptyTy
  , anyTy
  , trueTy
  , falseTy
  , stringTy
  , boolTy
  , anyArrowTy
  , anyProdTy
  , readBackTy
  ) where

-- This file implements set-theoretic types using the
-- techniques described by Giuseppe Castagna in his
-- manuscript "Covariance and Contravariance: a
-- fresh look at an old issue (a primer in advanced
-- type systems for learning functional programmers)".
-- Many thanks to Giuseppe for taking the time to write
-- and make public that manuscript! -A.M. Kent 2018

import Types.Base
import qualified Data.List as List
import qualified Types.Syntax as Stx
import qualified Data.Bits as Bits
import qualified Data.Map.Strict as Map

data Arrow = Arrow Ty Ty
  deriving (Eq, Show, Ord)

data Prod = Prod Ty Ty
  deriving (Eq, Show, Ord)

data BDD x where
  Top  :: BDD x
  Bot  :: BDD x
  Node :: (Eq x, Show x, Ord x) =>
    x -> (BDD x) -> (BDD x) -> (BDD x) -> (BDD x)

deriving instance Show x => Show (BDD x)
deriving instance Eq x => Eq (BDD x)
deriving instance (Eq x, Ord x) => Ord (BDD x)

-- a DNF representation of types
data Ty =
  Ty Base (BDD Prod) (BDD Arrow)
  | Var String  -- type variable (meaning given by an Env)
  deriving (Eq, Show, Ord)

-- type environment (i.e. mapping type names to types)
type Env = Map.Map String -> Ty

resolve :: String -> Env -> Ty
resolve name env = env Map.! name

extend :: String -> Ty -> Env -> Env
extend name t env = Map.insert name t env

-- universal type
anyTy = Ty anyBase Top Top
-- empty type
emptyTy = Ty emptyBase Bot Bot

-- some base types
trueTy  = parseTy Stx.T
falseTy = parseTy Stx.F
stringTy = parseTy Stx.Str
boolTy = tyOr' [trueTy, falseTy]


-- Constructs the type `t1 × t2`.
prodTy :: Ty -> Ty -> Ty
prodTy t1 t2 = (Ty emptyBase (node (Prod t1 t2) Top Bot Bot) Bot)

-- universal product
anyProdTy = prodTy anyTy anyTy

-- Constructs the type `t1 → t2`.
arrowTy :: Ty -> Ty -> Ty
arrowTy t1 t2 = (Ty emptyBase Bot (node (Arrow t1 t2) Top Bot Bot))

-- universal arrow
anyArrowTy = arrowTy emptyTy anyTy


-- Smart constructor for BDD nodes, performing
-- some basic simplifications.
node :: (Eq x, Show x, Ord x) =>
  x -> BDD x -> BDD x -> BDD x -> BDD x
node x l Top r = Top
node x l m r
  | l == r = (bddOr l m)
  | otherwise = Node x l m r


bddOr :: BDD x -> BDD x -> BDD x
bddOr Top _ = Top
bddOr _ Top = Top
bddOr Bot b = b
bddOr b Bot = b
bddOr b1@(Node a1 l1 m1 r1) b2@(Node a2 l2 m2 r2) =
  case compare a1 a2 of
    LT -> node a1 l1 (bddOr m1 b2) r1
    GT -> node a2 l2 (bddOr b1 m2) r2
    EQ -> if (l1 == l2) && (m1 == m2) && (r1 == r2)
          then b1
          else (node a1
                (bddOr l1 l2)
                (bddOr m1 m2)
                (bddOr r1 r2))

bddAnd :: BDD x -> BDD x -> BDD x
bddAnd Top b = b
bddAnd b Top = b
bddAnd Bot _ = Bot
bddAnd _ Bot = Bot
bddAnd b1@(Node a1 l1 m1 r1) b2@(Node a2 l2 m2 r2) =
  case compare a1 a2 of
    LT -> node a1 (bddAnd l1 b2) (bddAnd m1 b2) (bddAnd r1 b2)
    GT -> node a2 (bddAnd b1 l2) (bddAnd b1 m2) (bddAnd b1 r2)
    EQ -> if (l1 == l2) && (m1 == m2) && (r1 == r2)
          then b1
          else (node a1
                (bddAnd (bddOr l1 m1) (bddOr l2 m2))
                Bot
                (bddAnd (bddOr r1 m1) (bddOr r2 m2)))


bddDiff :: BDD x -> BDD x -> BDD x
bddDiff Bot _ = Bot
bddDiff _ Top = Bot
bddDiff b Bot = b
bddDiff Top b = bddNot b
bddDiff b1@(Node a1 l1 m1 r1) b2@(Node a2 l2 m2 r2) =
  case compare a1 a2 of
    LT -> (node a1
           (bddDiff (bddOr l1 m1) b2)
           Bot
           (bddDiff (bddOr r1 m1) b2))
    GT -> (node a2
           (bddDiff b1 (bddOr l2 m2))
           Bot
           (bddDiff b1 (bddOr r2 m2)))
    EQ -> if (l1 == l2) && (m1 == m2) && (r1 == r2)
          then Bot
          else (node a1
                (bddDiff l1 b2)
                (bddDiff m1 b2)
                (bddDiff r1 b2))

bddNot :: BDD x -> BDD x
bddNot Top = Bot
bddNot Bot = Top
bddNot (Node a l m Bot) = (node a Bot (bddAnd notM notL) notM)
  where notM = bddNot m
        notL = bddNot l
bddNot (Node a Bot m r) = (node a notM (bddAnd notM notR) Bot)
  where notM = bddNot m
        notR = bddNot r
bddNot (Node a l Bot r) = (node a notL (bddAnd notL notR) notR)
  where notL = bddNot l
        notR = bddNot r
bddNot (Node a l m r) = (node a (bddAnd notL notM) Bot (bddAnd notR notM))
  where notL = bddNot l
        notM = bddNot m
        notR = bddNot r


tyAnd :: Env -> Ty -> Ty -> Ty
tyAnd (Ty base1 prod1 arrow1) (Ty base2 prod2 arrow2) =
  (Ty (baseAnd base1 base2)
    (bddAnd prod1 prod2)
    (bddAnd arrow1 arrow2))
tyAnd env (Var name) t2 = tyAnd env (resolve name env) t2
tyAnd env t1 (Var name) = tyAnd env t1 (resolve name env)

tyAnd' :: Env -> [Ty] -> Ty
tyAnd' env ts = foldr (tyAnd env) anyTy ts

tyOr :: Env -> Ty -> Ty -> Ty
tyOr (Ty base1 prod1 arrow1) (Ty base2 prod2 arrow2) =
  (Ty (baseOr base1 base2)
    (bddOr prod1 prod2)
    (bddOr arrow1 arrow2))
tyOr env (Var name) t2 = tyOr env (resolve name env) t2
tyOr env t1 (Var name) = tyOr env t1 (resolve name env)


tyOr' :: Env -> [Ty] -> Ty
tyOr' env ts = foldr (tyOr env) emptyTy ts

tyDiff :: Env -> Ty -> Ty -> Ty
tyDiff env (Ty base1 prod1 arrow1) (Ty base2 prod2 arrow2) =
  (Ty (baseDiff base1 base2)
    (bddDiff prod1 prod2)
    (bddDiff arrow1 arrow2))
tyDiff env (Var name) t2 = tyDiff env (resolve name env) t2
tyDiff env t1 (Var name) = tyDiff env t1 (resolve name env)


tyNot :: Env -> Ty -> Ty
tyNot env t = tyDiff env anyTy t




parseTy :: Stx.Ty -> Ty
parseTy (Stx.Prod t1 t2) = (prodTy
                               (parseTy t1)
                               (parseTy t2))
parseTy (Stx.Arrow t1 t2) = (arrowTy
                                (parseTy t1)
                                (parseTy t2))
parseTy (Stx.Or []) = emptyTy
parseTy (Stx.Or (t:ts)) = (foldr tyOr
                             (parseTy t)
                             (map parseTy ts))
parseTy (Stx.And []) = anyTy
parseTy (Stx.And (t:ts)) = (foldr tyAnd
                              (parseTy t)
                              (map parseTy ts))
parseTy (Stx.Not t) = tyNot (parseTy t)
parseTy Stx.Any = anyTy
parseTy Stx.Empty = emptyTy
parseTy (Stx.Var name) = Var name
parseTy (Stx.Base b) = Ty (Base True (Bits.bit $ Stx.baseIndex b))

anyProdStr = "(Prod Any Any)"
anyArrowStr = "(Arrow Empty Any)"
anyBaseStr = "(Not (Or (Prod Any Any) (Arrow Empty Any)))"

-- reads a Ty (from LazyBDD) into an sexpression
-- that Repl/Parser.hs can read in
readBackTy :: Ty -> String
readBackTy (Ty b@(Base True n) Bot Bot)
  | n == 0 = "Empty"
  | otherwise = readBackBase b
readBackTy (Ty b@(Base False n) Top Top)
  | n == 0 = "Any"
  | otherwise = readBackBase b
readBackTy (Ty bs ps as) = strOr t1 $ strOr t2 t3
  where t1 = strAnd anyBaseStr $ readBackBase bs
        t2 = strAnd anyProdStr $ readBackBDD readBackProd ps
        t3 = strAnd anyArrowStr$ readBackBDD readBackArrow as
readBackTy (Var name) = name

strOr :: String -> String -> String
strOr "Any" _ = "Any"
strOr _ "Any" = "Any"
strOr "Empty" str = str
strOr str "Empty" = str
strOr str1 str2 = if str1 == str2
                  then str1
                  else "(Or " ++ str1 ++ " " ++  str2 ++  ")"

strAnd :: String -> String -> String
strAnd "Empty" _ = "Empty"
strAnd _ "Empty" = "Empty"
strAnd "Any" str = str
strAnd str "Any" = str
strAnd str1 str2 = if str1 == str2
                   then str1
                   else "(And " ++ str1 ++ " " ++  str2 ++  ")"

strNot :: String -> String
strNot "Any" = "Empty"
strNot "Empty" = "Any"
strNot str = "(Not " ++ str ++ ")"

readBackBDD :: (x -> String) -> (BDD x) -> String
readBackBDD readBackAtom Top = "Any"
readBackBDD readBackAtom Bot = "Empty"
readBackBDD readBackAtom (Node a l m r) = strOr t1 $ strOr t2 t3
  where aStr = readBackAtom a
        t1 = strAnd aStr $ continue l
        t2 = continue m
        t3 = strAnd (strNot aStr) $ continue r
        continue = readBackBDD readBackAtom
        

readBackBase :: Base -> String
readBackBase (Base b 0) = if b then "Empty" else "Any"
readBackBase (Base True b) = foldr strOr "Empty" bases
  where bases = [Stx.baseTyStr t | (t,idx) <- zip Stx.baseTypes [0..], Bits.testBit b idx]
readBackBase (Base False b) = strNot $ readBackBase (Base True b)

readBackArrow :: Arrow -> String
readBackArrow (Arrow t1 t2) = "(Arrow " ++ str1 ++ " " ++ str2 ++ ")"
  where str1 = readBackTy t1
        str2 = readBackTy t2

readBackProd :: Prod -> String
readBackProd (Prod t1 t2) = "(Prod " ++ str1 ++ " " ++ str2 ++ ")"
  where str1 = readBackTy t1
        str2 = readBackTy t2



