{-# LANGUAGE GADTs, StandaloneDeriving #-}
module Types.LazyBDD
  ( Ty(..)
  , Env(..)
  , BDD(..)
  , Arrow(..)
  , Prod(..)
  , mtEnv
  , extend
  , resolve
  , envMember
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
  , nullTy
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
import Data.Map (Map)
import qualified Data.Map as Map


data BDD x where
  Top  :: BDD x
  Bot  :: BDD x
  Node :: (Eq x, Show x, Ord x) =>
    x -> (BDD x) -> (BDD x) -> (BDD x) -> (BDD x)

deriving instance Show x => Show (BDD x)
deriving instance Eq x => Eq (BDD x)
deriving instance (Eq x, Ord x) => Ord (BDD x)



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

data Arrow = Arrow Ty Ty
  deriving (Eq, Show, Ord)

data Prod = Prod Ty Ty
  deriving (Eq, Show, Ord)


-- For now we assume Environments always are extended with
-- unique names and there is never any shadowing (the parser
-- checks for this when new type names are defined), so just
-- using String works fine.
newtype Name = Name String

instance Eq Name where
  (Name name1 _ _ _) == (Name name2 _ _ _) = name1 == name2
instance Ord Name where
  compare (Name name1 _ _ _) (Name name2 _ _ _) = compare name1 name2
instance Show Name where
  show (Name name _ _ _) = name


-- This BDD is just used to represent the unfolded back-edges into
-- cyclic types. We can then these these for equality and ordering
-- instead of the lazy, infinite graphs for cyclic types.
type FiniteTy = (BDD (Either Name (Base,(BDD Prod),(BDD Arrow))))

data Ty where
  TyLeaf :: Base (BDD Prod) (BDD Arrow)
  TyNode :: FiniteTy Base (BDD Prod) (BDD Arrow)
-- In order to keep even our infinite types "finite",
-- we only reason about their finite components (in
-- other words, the DNF on the rhs of TyNode is not
-- included in Eq, Ord, or Show, since it contains
-- the unfolding of Name (the first element in
-- the tuple on the LHS)

instance Eq Ty where
  (TyLeaf b1 p1 a1) == (TyLeaf b2 p2 a2) = b1 == b2 && p1 == p2 && a1 == a2
  (TyLeaf _ _ _)    == (TyNode _ _ _ _)  = False
  (TyNode _ _ _ _)  == (TyLeaf _ _ _)    = False
  (TyNode ft1 _ _ _) == (TyNode ft2 _ _ _) = ft1 == ft2
  
instance Ord Name where
  compare (TyLeaf b1 p1 a1) (TyLeaf b2 p2 a2) =
    case compare b1 b2 of
      LT -> LT
      GT -> GT
      EQ -> case compare p1 p2 of
              LT -> LT
              GT -> GT
              EQ -> compare a1 a2
  compare (TyLeaf _) (TyNode _ _)     = LT
  compare (TyNode _ _) (TyLeaf _)     = GT
  compare (TyNode ft1 _ _ _) (TyNode ft2 _ _ _) = compare ft1 ft2
  
instance Show Name where
  show (TyLeaf b p a)   = "TyLeaf " ++ show b ++ " " ++ show p ++ " " ++ show a
  show (TyNode ft _ _ _) = "TyNode " ++ show ft
  





-- type environment (i.e. mapping type names to types)
type Env = Map String Ty

mtEnv :: Env
mtEnv = Map.empty

envMember :: String -> Env -> Bool
envMember name env = Map.member name env

resolve :: String -> Env -> Maybe Ty
resolve name env = Map.lookup name env 

extend :: String -> Ty -> Env -> Env
extend name t env = Map.insert name t env

-- universal type
anyTy = TyLeaf $ DNF anyBase Top Top
-- empty type
emptyTy = TyLeaf $ DNF emptyBase Bot Bot

-- some base types
trueTy  = parseTy mtEnv $ Stx.Base Stx.T
falseTy = parseTy mtEnv $ Stx.Base Stx.F
stringTy = parseTy mtEnv $ Stx.Base Stx.Str
nullTy = parseTy mtEnv $ Stx.Base Stx.Null
boolTy = tyOr trueTy falseTy

nameNode :: String -> (BDD FiniteTy)
nameNode name = node (Left name) Top Bot Bot

bddNode :: Base -> (BDD Prod) -> (BDD Arrow) -> (BDD FiniteTy)
bddNode (Base False 0) Top Top = Top
bddNode (Base True 0) Bot Bot = Bot
bddNode b p a = node (Right (b,p,a)) Top Bot Bot

-- constructs a named type, whose full description is the given dnf
nameTy :: String -> Ty -> Ty
nameTy name (TyLeaf b p a) = TyNode (Left (nameNode name)) b p a


-- Constructs the type `t1 × t2`.
prodTy :: Ty -> Ty -> Ty
prodTy t1 t2 = TyLeaf $ DNF emptyBase (node (Prod t1 t2) Top Bot Bot) Bot

-- universal product
anyProdTy = prodTy anyTy anyTy

-- Constructs the type `t1 → t2`.
arrowTy :: Ty -> Ty -> Ty
arrowTy t1 t2 = TyLeaf $  DNF emptyBase Bot (node (Arrow t1 t2) Top Bot Bot)

-- universal arrow
anyArrowTy = arrowTy emptyTy anyTy



tyAnd :: Ty -> Ty -> Ty
tyAnd (TyLeaf b1 p1 a1) (TyLeaf b2 p2 a2) = TyLeaf b p a
  where b = baseAnd b1 b2
        p = bddAnd p1 p2
        a = bddAnd a1 a2
tyAnd (TyNode fty1 b1 p1 a1) (TyLeaf b2 p2 a2) = TyNode fty b p a
  where fty = bddAnd fty1 (bddNode b2 p2 a2)
        b   = bddAnd b1 b2
        p   = bddAnd p1 p2
        a   = bddAnd a1 a2
tyAnd (TyLeaf b1 p1 a1) (TyNode fty2 b2 p2 a2) = TyNode fty b p a
  where fty = bddAnd (bddNode b1 p1 a1) fty2
        b   = bddAnd b1 b2
        p   = bddAnd p1 p2
        a   = bddAnd a1 a2
tyAnd (TyNode fty1 b1 p1 a1) (TyNode fty2 b2 p2 a2) = TyNode fty b p a
  where fty = bddAnd fty1 fty2
        b   = bddAnd b1 b2
        p   = bddAnd p1 p2
        a   = bddAnd a1 a2


tyAnd' :: [Ty] -> Ty
tyAnd' ts = foldr tyAnd anyTy ts


-- BOOKMARK tyAnd is done (I think), do the rest!
tyOr :: Ty -> Ty -> Ty
tyOr (TyLeaf (DNF b1 p1 a1)) (TyLeaf (DNF b2 p2 a2)) = TyLeaf $ DNF b p a
  where b = baseOr b1 b2
        p = bddOr p1 p2
        a = bddOr a1 a2
tyOr (TyNode (name,l,m,r) bdd) _ = error "TODO"
tyOr _ (TyNode (name,l,m,r) bdd) = error "TODO"


tyOr' :: [Ty] -> Ty
tyOr' ts = foldr tyOr emptyTy ts

tyDiff :: Ty -> Ty -> Ty
tyDiff (Ty (DNF b1 p1 a1)) (Ty (DNF b2 p2 a2)) = Ty b p a
  where b = baseDiff b1 b2
        p = bddDiff p1 p2
        a = bddDiff a1 a2
tyDiff (TyNode (name,l,m,r) bdd) _ = error "TODO"
tyDiff _ (TyNode (name,l,m,r) bdd) = error "TODO"


tyNot :: Ty -> Ty
tyNot t = tyDiff anyTy t




parseTy :: Env -> Stx.Ty -> Ty
parseTy env (Stx.Prod t1 t2) = prodTy (parseTy env t1) (parseTy env t2)
parseTy env (Stx.Arrow t1 t2) = arrowTy (parseTy env t1) (parseTy env t2)
parseTy env (Stx.Or ts) = foldr (tyOr env) emptyTy $ map (parseTy env) ts
parseTy env (Stx.And ts) = foldr (tyAnd env) anyTy $ map (parseTy env) ts
parseTy env (Stx.Not t) = tyNot env (parseTy env t)
parseTy env Stx.Any = anyTy
parseTy env Stx.Empty = emptyTy
parseTy env (Stx.Name name) = Name name
parseTy env (Stx.Base bTy) = Ty b Bot Bot
  where b = Base True $ Bits.bit $ Stx.baseIndex bTy

anyProdStr = "(Prod Any Any)"
anyArrowStr = "(Arrow Empty Any)"
anyBaseStr = "(Not (Or (Prod Any Any) (Arrow Empty Any)))"

-- reads a Ty (from LazyBDD) into an sexpression
-- that Repl/Parser.hs can read in
readBackTy :: Ty -> String
readBackTy (TyLeaf b@(Base True n) Bot Bot)
  | n == 0 = "Empty"
  | otherwise = readBackBase b
readBackTy (TyLeaf b@(Base False n) Top Top)
  | n == 0 = "Any"
  | otherwise = readBackBase b
readBackTy (TyLeaf (DNF bs ps as)) = strOr t1 $ strOr t2 t3
  where t1 = strAnd anyBaseStr $ readBackBase bs
        t2 = strAnd anyProdStr $ readBackBDD readBackProd ps
        t3 = strAnd anyArrowStr$ readBackBDD readBackArrow as
readBackTy (Name name) = name

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



