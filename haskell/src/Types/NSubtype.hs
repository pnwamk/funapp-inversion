module Types.NSubtype
  ( overlap
  , subtype
  , equiv
  , isEmpty
  , flattenProds
  , flattenBDD
  ) where

-- A naive (i.e. inefficient) implementation of subtyping for set
-- theoretic types... and a potentially useful oracle for more
-- efficient implementation experimentation!

import           Types.LazyBDD
import           Data.List
import           Common.SetOps
import           Control.Applicative
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Maybe
import           Control.Applicative
import           Data.Foldable

-- Is this type equivalent to ∅?
isEmpty :: Ty -> Bool
isEmpty t = isJust $ mtTy t Set.empty

type Seen = Set FiniteTy

-- internal isEmpty which tracks seen types
mtTy :: Ty -> Seen -> Maybe Seen
mtTy (Ty b ps as) seen
  | not $ b == emptyBase = Nothing
  | otherwise = mtProd ps seen >>=  mtArrow as
mtTy t@(TyNode fty b ps as) seen
  | Set.member fty seen  = Just seen
  | not $ b == emptyBase = Nothing
  | otherwise = mtProd ps (Set.insert fty seen) >>= mtArrow as


-- given a BDD of Prods, return the flattened
-- list representations of the positive
-- and negative components, e.g.:
-- (⋃((S×S) ∩ (⋂ ¬(T×T) ...))) 
flattenProds :: (BDD Prod) -> [(Prod , [Prod])]
flattenProds prods = flattenAux anyTy anyTy [] prods
  where flattenAux :: Ty -> Ty -> [Prod] -> (BDD Prod) -> [(Prod , [Prod])]
        flattenAux t1 t2 negAtoms Top = [((Prod t1 t2) , negAtoms)]
        flattenAux t1 t2 negAtoms Bot = []
        flattenAux t1 t2 negAtoms (Node p@(Prod t3 t4) l m r) =
          ((flattenAux (tyAnd t1 t3) (tyAnd t2 t4) negAtoms l)
           ++ (flattenAux t1 t2 negAtoms m)
           ++ (flattenAux t1 t2 (p:negAtoms) r))


-- Is a BDD of prods equivalent to ∅?
-- For each clause in the DNF of the product type,
-- let the positive info P be (S₁, S₂) and negative info
-- N be (¬(T₁,T₂),...), check that for all N' ⊆ N,
-- (s1 <: (⋃(T₁,T₂) ∈ N' T₁)) or (s2 <: (⋃(T₁,T₂) ∈ N\N' T₂))
-- i.e. that all possible combinations of the negative info
-- would produce an empty type in either the first or second
-- field of the product type.
mtProd :: (BDD Prod) -> Seen -> Maybe Seen
mtProd ps initialSeen = foldrM emptyClause initialSeen (flattenProds ps)
  where emptyClause :: (Prod , [Prod]) -> Seen -> Maybe Seen
        emptyClause ((Prod s1 s2) , negs) seen =
          foldrM (emptyProd s1 s2 negs) seen (subsets negs)
        emptyProd :: Ty -> Ty -> [Prod] -> [Prod] -> Seen -> Maybe Seen
        emptyProd s1 s2 negs negs' seen =
          mtTy (tyDiff s1 (orFsts negs')) seen
          <|> mtTy (tyDiff s2 (orSnds (negs \\ negs'))) seen
        orFsts :: [Prod] -> Ty
        orFsts ps = foldr (\(Prod t1 _) t -> tyOr t t1) emptyTy ps
        orSnds :: [Prod] -> Ty
        orSnds ps = foldr (\(Prod _ t2) t -> tyOr t t2) emptyTy ps



-- given a BDD of x, return the flattened
-- list representations of the positive
-- and negative components, e.g.:
-- (⋃(⋂ x ...) ∩ (⋂ ¬x ...))) 
flattenBDD :: (BDD x) -> [([x] , [x])]
flattenBDD as = flattenAux [] [] as
  where flattenAux :: [x] -> [x] -> (BDD x)
          -> [([x] , [x])]
        flattenAux pos neg Bot = []
        flattenAux pos neg Top = [(pos,neg)]
        flattenAux pos neg (Node a l m r) =
          ((flattenAux (a:pos) neg l)
           ++ (flattenAux pos neg m)
           ++ (flattenAux pos (a:neg) r))




-- Is a BDD of arrows equivalent to ∅?
-- For each clause in the DNF of the arrow type,
-- let the positive info be P be (¬(T₁ → T₂),...) and the
-- negative info N be (¬(T₁ → T₂),...), check that for some
-- (T₁ → T₂) ∈ N, T₁ <: ⋃(S₁ ...) and for all non-empty P' ⊆ P
-- (T₁ <: ⋃(S₁→S₂ ∈ P\P') S₁) or (⋂(S₁→S₂ ∈ P') S₂ <: T₂)
mtArrow :: (BDD Arrow) -> Seen -> Maybe Seen
mtArrow as initialSeen = foldrM emptyClause initialSeen (flattenBDD as)
  where emptyClause :: ([Arrow] , [Arrow]) -> Seen -> Maybe Seen
        emptyClause (pos,neg) seen =
          case mapMaybe (emptyArrow dom pos seen) neg of
            [] -> Nothing
            (seen':_) -> Just seen'
          where dom = foldr (\(Arrow s1 _) t -> tyOr t s1) emptyTy pos
        emptyArrow :: Ty -> [Arrow] -> Seen -> Arrow -> Maybe Seen
        emptyArrow dom pos seen (Arrow t1 t2) = do
          seen' <- mtTy (tyDiff t1 dom) seen
          foldrM (emptyHelper t1 t2 pos) seen' (nonEmptySubsets pos)
        emptyHelper :: Ty -> Ty -> [Arrow] -> [Arrow] -> Seen -> Maybe Seen
        emptyHelper t1 t2 pos pos' seen =
          mtTy (tyDiff t1 dom) seen <|> mtTy (tyDiff rng t2) seen
          where dom = (foldr (\(Arrow s1 _) t -> tyOr t s1)
                       emptyTy
                       (pos \\ pos'))
                rng = (foldr (\(Arrow _ s2) t -> tyAnd t s2)
                        anyTy
                        pos')

-- is [[t1]] ∩ [[t2]] ≠ ∅
overlap :: Ty -> Ty -> Bool
overlap t1 t2 = not $ isEmpty $ tyAnd t1 t2


-- Is t1 a subtype of t2
-- i.e. [[t1]] ⊆ [[t2]]
subtype :: Ty -> Ty -> Bool
subtype t1 t2 = isEmpty $ tyDiff t1 t2


-- Is t1 equivalent to t2
-- i.e. [[t1]] ⊆ [[t2]] and [[t1]] ⊇ [[t2]]
equiv :: Ty -> Ty -> Bool
equiv t1 t2 = subtype t1 t2 && subtype t2 t1
