{-# LANGUAGE GADTs, StandaloneDeriving, RankNTypes #-}
module Types.LazyBDD
  ( Ty(..)
  , FiniteTy(..)
  , Env(..)
  , BDD(..)
  , Arrow(..)
  , Prod(..)
  , tyProds
  , tyArrows
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
  , emptyBase
  , anyBase
  ) where

-- This file implements set-theoretic types using the
-- techniques described by Giuseppe Castagna in his
-- manuscript "Covariance and Contravariance: a
-- fresh look at an old issue (a primer in advanced
-- type systems for learning functional programmers)".
-- Many thanks to Giuseppe for taking the time to write
-- and make public that manuscript! -A.M. Kent 2018

import           Data.Word
import           Data.Bits
import qualified Data.List as List
import qualified Types.Syntax as Stx
import qualified Data.Bits as Bits
import           Data.Map (Map)
import qualified Data.Map as Map

------------------------------------------------------------
-- Base type DNF representation
------------------------------------------------------------
-- base types are disjoint, and thus their DNF can be
-- represented with finite sets and a flag, indicating
-- either (U b_1 ... b_n) or ¬(U b_1 b_2). We are
-- interested in a particular, fixed set of base types,
-- so we further optimize this representation by using a
-- bitfield to represent the union portion

(.\\.) :: Bits a => a -> a -> a
b1 .\\. b2 = b1 .&. (complement b2)

data Base = Base Bool Word64
  deriving (Eq, Show, Ord)

emptyBase = Base True 0
anyBase   = Base False 0


baseOr :: Base -> Base -> Base
baseOr (Base True pos1)  (Base True pos2)  = Base True  $ pos1 .|. pos2
baseOr (Base True pos)   (Base False neg)  = Base False $ neg .\\. pos
baseOr (Base False neg)  (Base True pos)   = Base False $ neg .\\. pos
baseOr (Base False neg1) (Base False neg2) = Base False $ neg1 .&. neg2

baseAnd :: Base -> Base -> Base
baseAnd (Base True pos1)  (Base True pos2)  = Base True $ pos1 .&. pos2
baseAnd (Base True pos)   (Base False neg)  = Base True $ pos .\\. neg
baseAnd (Base False neg)  (Base True pos)   = Base True $ pos .\\. neg
baseAnd (Base False neg1) (Base False neg2) = Base False $ neg1 .|. neg2


baseDiff :: Base -> Base -> Base
baseDiff (Base True pos1)  (Base True pos2)  = Base True $ pos1 .\\. pos2
baseDiff (Base True pos)   (Base False neg)  = Base True $ pos .&. neg
baseDiff (Base False neg)  (Base True pos)   = Base False $ pos .|. neg
baseDiff (Base False neg1) (Base False neg2) = Base True $ neg2 .\\. neg1

baseNot :: Base -> Base
baseNot (Base sign bs) = Base (not sign) bs


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
  | l == r    = bddOr l m
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
    EQ | ((l1 == l2) && (m1 == m2) && (r1 == r2)) -> b1
       | otherwise -> let l = bddOr l1 l2
                          m = bddOr m1 m2
                          r = bddOr r1 r2
                      in node a1 l m r
            

bddAnd :: BDD x -> BDD x -> BDD x
bddAnd Top b = b
bddAnd b Top = b
bddAnd Bot _ = Bot
bddAnd _ Bot = Bot
bddAnd b1@(Node a1 l1 m1 r1) b2@(Node a2 l2 m2 r2) =
  case compare a1 a2 of
    LT -> let l = bddAnd l1 b2
              m = bddAnd m1 b2
              r = bddAnd r1 b2
          in node a1 l m r
    GT -> let l = bddAnd b1 l2
              m = bddAnd b1 m2
              r = bddAnd b1 r2
          in node a2 l m r
    EQ | (l1 == l2) && (m1 == m2) && (r1 == r2) -> b1
       | otherwise -> let l = bddAnd (bddOr l1 m1) (bddOr l2 m2)
                          r = bddAnd (bddOr r1 m1) (bddOr r2 m2)
                     in node a1 l Bot r


bddDiff :: BDD x -> BDD x -> BDD x
bddDiff Bot _ = Bot
bddDiff _ Top = Bot
bddDiff b Bot = b
bddDiff Top b = bddNot b
bddDiff b1@(Node a1 l1 m1 r1) b2@(Node a2 l2 m2 r2) =
  case compare a1 a2 of
    LT -> let l = bddDiff (bddOr l1 m1) b2
              r = bddDiff (bddOr r1 m1) b2
          in node a1 l Bot r
    GT -> let l = bddDiff b1 (bddOr l2 m2)
              r = bddDiff b1 (bddOr r2 m2)
          in node a2 l Bot r
    EQ | (l1 == l2) && (m1 == m2) && (r1 == r2) -> Bot
       | otherwise -> let l = bddDiff l1 b2
                          m = bddDiff m1 b2
                          r = bddDiff r1 b2
                      in node a1 l m r

bddNot :: BDD x -> BDD x
bddNot Top = Bot
bddNot Bot = Top
bddNot (Node a l m Bot) = node a Bot (bddAnd notM notL) notM
  where notM = bddNot m
        notL = bddNot l
bddNot (Node a Bot m r) = node a notM (bddAnd notM notR) Bot
  where notM = bddNot m
        notR = bddNot r
bddNot (Node a l Bot r) = node a notL (bddAnd notL notR) notR
  where notL = bddNot l
        notR = bddNot r
bddNot (Node a l m r) = node a (bddAnd notL notM) Bot (bddAnd notR notM)
  where notL = bddNot l
        notM = bddNot m
        notR = bddNot r


-- arrow and product type atoms for their respective BDDs
data Arrow = Arrow Ty Ty
  deriving (Eq, Show, Ord)
data Prod = Prod Ty Ty
  deriving (Eq, Show, Ord)


-- For now we assume Environments always are extended with
-- unique names and there is never any shadowing (the parser
-- checks for this when new type names are defined), so just
-- using String works fine.
newtype Name = Name String
  deriving (Eq, Ord, Show)


-- This BDD is used to represent the unfolded back-edges
-- into cyclic types. We can then these these for equality
-- and ordering instead of the lazy, infinite graphs for
-- cyclic types.
type FiniteTy = BDD (Either Name (Base, BDD Prod, BDD Arrow))

data Ty =
    Ty Base (BDD Prod) (BDD Arrow)
  | TyNode FiniteTy Base (BDD Prod) (BDD Arrow)
-- In order to keep even our infinite types "finite",
-- we only reason about their finite components (in
-- other words, the DNF on the rhs of TyNode is not
-- included in Eq, Ord, or Show, since it contains
-- the unfolding of Name (the first element in
-- the tuple on the LHS)

instance Eq Ty where
  (Ty b1 p1 a1) == (Ty b2 p2 a2) = b1 == b2 && p1 == p2 && a1 == a2
  (Ty _ _ _)    == (TyNode _ _ _ _)  = False
  (TyNode _ _ _ _)  == (Ty _ _ _)    = False
  (TyNode ft1 _ _ _) == (TyNode ft2 _ _ _) = ft1 == ft2
  
instance Ord Ty where
  compare (Ty b1 p1 a1) (Ty b2 p2 a2) =
    case compare b1 b2 of
      LT -> LT
      GT -> GT
      EQ -> case compare p1 p2 of
              LT -> LT
              GT -> GT
              EQ -> compare a1 a2
  compare (Ty _ _ _) (TyNode _ _ _ _) = LT
  compare (TyNode _ _ _ _) (Ty _ _ _) = GT
  compare (TyNode ft1 _ _ _) (TyNode ft2 _ _ _) = compare ft1 ft2
  
instance Show Ty where
  show (Ty b p a)   = "Ty " ++ show b ++ " " ++ show p ++ " " ++ show a
  show (TyNode ft _ _ _) = "TyNode " ++ show ft
  

tyProds :: Ty -> (BDD Prod)
tyProds (Ty       _ p _) = p
tyProds (TyNode _ _ p _) = p

tyArrows :: Ty -> (BDD Arrow)
tyArrows (Ty       _ _ a) = a
tyArrows (TyNode _ _ _ a) = a



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
anyTy = Ty anyBase Top Top
-- empty type
emptyTy = Ty emptyBase Bot Bot

-- some base types
trueTy  = parseTy mtEnv $ Stx.Base Stx.T
falseTy = parseTy mtEnv $ Stx.Base Stx.F
stringTy = parseTy mtEnv $ Stx.Base Stx.Str
nullTy = parseTy mtEnv $ Stx.Base Stx.Null
boolTy = tyOr trueTy falseTy

nameFiniteTy :: Name -> FiniteTy
nameFiniteTy name = node (Left name) Top Bot Bot

bddFiniteTy :: Base -> (BDD Prod) -> (BDD Arrow) -> FiniteTy
bddFiniteTy (Base False 0) Top Top = Top
bddFiniteTy (Base True 0) Bot Bot = Bot
bddFiniteTy b p a = node (Right (b,p,a)) Top Bot Bot

-- constructs a named type, whose full description is the given dnf
nameTy :: Name -> Ty -> Ty
nameTy name (Ty b p a) = TyNode fty b p a
  where fty = nameFiniteTy name
nameTy name (TyNode _ b p a) = TyNode fty b p a
  where fty = nameFiniteTy name


-- Constructs the type `t1 × t2`.
prodTy :: Ty -> Ty -> Ty
prodTy t1 t2 = Ty emptyBase (node (Prod t1 t2) Top Bot Bot) Bot

-- universal product
anyProdTy = prodTy anyTy anyTy

-- Constructs the type `t1 → t2`.
arrowTy :: Ty -> Ty -> Ty
arrowTy t1 t2 = Ty emptyBase Bot (node (Arrow t1 t2) Top Bot Bot)

-- universal arrow
anyArrowTy = arrowTy emptyTy anyTy

tyBinop :: (Base -> Base -> Base) -> (forall x. BDD x -> BDD x -> BDD x) -> Ty -> Ty -> Ty 
tyBinop baseBinop bddBinop = binop
  where binop (Ty b1 p1 a1) (Ty b2 p2 a2) = Ty b p a
          where b = baseBinop b1 b2
                p = bddBinop p1 p2
                a = bddBinop a1 a2
        binop (TyNode fty1 b1 p1 a1) (Ty b2 p2 a2) = TyNode fty b p a
          where fty = bddBinop fty1 (bddFiniteTy b2 p2 a2)
                b   = baseBinop b1 b2
                p   = bddBinop p1 p2
                a   = bddBinop a1 a2
        binop (Ty b1 p1 a1) (TyNode fty2 b2 p2 a2) = TyNode fty b p a
          where fty = bddBinop (bddFiniteTy b1 p1 a1) fty2
                b   = baseBinop b1 b2
                p   = bddBinop p1 p2
                a   = bddBinop a1 a2
        binop (TyNode fty1 b1 p1 a1) (TyNode fty2 b2 p2 a2) = TyNode fty b p a
          where fty = bddBinop fty1 fty2
                b   = baseBinop b1 b2
                p   = bddBinop p1 p2
                a   = bddBinop a1 a2


tyAnd :: Ty -> Ty -> Ty
tyAnd = tyBinop baseAnd bddAnd


tyAnd' :: [Ty] -> Ty
tyAnd' ts = foldr tyAnd anyTy ts


tyOr :: Ty -> Ty -> Ty
tyOr = tyBinop baseOr bddOr


tyOr' :: [Ty] -> Ty
tyOr' ts = foldr tyOr emptyTy ts

tyDiff :: Ty -> Ty -> Ty
tyDiff = tyBinop baseDiff bddDiff

tyNot :: Ty -> Ty
tyNot = tyDiff anyTy




parseTy :: Env -> Stx.Ty -> Ty
parseTy env (Stx.Prod t1 t2) = prodTy (parseTy env t1) (parseTy env t2)
parseTy env (Stx.Arrow t1 t2) = arrowTy (parseTy env t1) (parseTy env t2)
parseTy env (Stx.Or ts) = foldr tyOr emptyTy $ map (parseTy env) ts
parseTy env (Stx.And ts) = foldr tyAnd anyTy $ map (parseTy env) ts
parseTy env (Stx.Not t) = tyNot $ parseTy env t
parseTy env Stx.Any = anyTy
parseTy env Stx.Empty = emptyTy
parseTy env (Stx.Name name) = nameTy (Name name) (env Map.! name)
parseTy env (Stx.Base bTy) = Ty b Bot Bot
  where b = Base True $ Bits.bit $ Stx.baseIndex bTy

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
readBackTy (TyNode fty _ _ _) = readBackBDD readBackNameOrTy fty

readBackNameOrTy :: Either Name (Base, BDD Prod, BDD Arrow) -> String
readBackNameOrTy (Left (Name name)) = name
readBackNameOrTy (Right (b,p,a)) = readBackTy $ Ty b p a

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



