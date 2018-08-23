{-# LANGUAGE GADTs, StandaloneDeriving #-}
module Types.LazyBDD
  ( Ty(..)
  , BDD(..)
  , Arrow(..)
  , Prod(..)
  , prodTy
  , parseTy
  , tyAnd
  , tyOr
  , tyDiff
  , tyNot
  , emptyTy
  , anyTy
  , anyArrow
  , anyProd
  , trueTy
  , falseTy
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
import qualified Data.Set as Set
import qualified Data.Bits as Bits
import qualified Data.Map as M


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
data Ty = Ty !Base !(BDD Prod) !(BDD Arrow)
  deriving(Eq, Show, Ord)

-- universal type
anyTy = Ty anyBase Top Top
-- empty type
emptyTy = Ty emptyBase Bot Bot

-- boolean types
trueTy  = parseTy Stx.T
falseTy = parseTy Stx.F

-- Constructs the type `t1 × t2`.
prodTy :: Ty -> Ty -> Ty
prodTy t1 t2 = (Ty emptyBase (node (Prod t1 t2) Top Bot Bot) Bot)

-- universal product
anyProd = prodTy anyTy anyTy

-- Constructs the type `t1 → t2`.
arrowTy :: Ty -> Ty -> Ty
arrowTy t1 t2 = (Ty emptyBase Bot (node (Arrow t1 t2) Top Bot Bot))

-- universal arrow
anyArrow = arrowTy emptyTy anyTy


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

{-# INLINE tyAnd #-}
tyAnd :: Ty -> Ty -> Ty
tyAnd (Ty base1 prod1 arrow1) (Ty base2 prod2 arrow2) =
  (Ty (baseAnd base1 base2)
    (bddAnd prod1 prod2)
    (bddAnd arrow1 arrow2))

{-# INLINE tyOr #-}
tyOr :: Ty -> Ty -> Ty
tyOr (Ty base1 prod1 arrow1) (Ty base2 prod2 arrow2) =
  (Ty (baseOr base1 base2)
    (bddOr prod1 prod2)
    (bddOr arrow1 arrow2))

{-# INLINE tyDiff #-}
tyDiff :: Ty -> Ty -> Ty
tyDiff (Ty base1 prod1 arrow1) (Ty base2 prod2 arrow2) =
  (Ty (baseDiff base1 base2)
    (bddDiff prod1 prod2)
    (bddDiff arrow1 arrow2))

{-# INLINE tyNot #-}
tyNot :: Ty -> Ty
tyNot t = tyDiff anyTy t






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
parseTy t = Ty (Base True $ Stx.baseTypeIndex t) Bot Bot
-- parseTy t = case M.lookup t Stx.baseTypesMap of
--               Nothing -> error ("Not a base type: " ++ (show t))
--               Just wd -> Ty (Base True wd) Bot Bot
-- parseTy t = case List.elemIndex t Stx.baseTypes of
--               Nothing -> error ("Not a base type: " ++ (show t))
--               Just idx -> Ty (Base True (Bits.bit idx)) Bot Bot

