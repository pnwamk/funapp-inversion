module Types.NMetafunctions
  ( isFun
  , isProd
  , fstProj
  , sndProj
  , domTy
  , rngTy
  , inTy
  ) where

import Types.LazyBDD
import Types.NSubtype (flattenProds, flattenBDD)
import Types.Subtype
import Data.List
import Common.SetOps

-- Is this a function type?
isFun :: Ty -> Bool
isFun t = subtype t anyArrowTy

-- Is this a function type?
isProd :: Ty -> Bool
isProd t = subtype t anyProdTy

data Index = First | Second
  deriving (Eq, Ord, Show)

-- Calculates the projection type for a given type
-- i.e. given (\(Prod t _) -> t) (prodTy T F)
--      it should produce T, also
--      given (\(Prod _ t) -> t) (prodTy T F)
--      it should produce F.
-- Works on complex types that are <: Any × Any.
-- Equivalent to ⋃i∈I(⋃N'⊆Nᵢ(⋂p∈Pᵢ Sₚ & ⋂n∈N' ¬Sₙ))
-- where the original product type is
-- ⋃i∈I(̱ ⋂p∈Pᵢ (Sₚ , Tₚ)  &  ⋂n∈Nᵢ  ¬(Sₙ , Tₙ) )
calcProj :: Index -> Ty -> Maybe Ty
calcProj idx t
  | not (isProd t) = Nothing
  | otherwise = Just $ foldl tyOr emptyTy clauses
    where clauses :: [Ty]
          clauses = map clauseProj $ flattenProds $ tyProds t
          clauseProj :: (Prod, [Prod]) -> Ty
          clauseProj ((Prod t1 t2), negs) = foldr projOr emptyTy negss
            where negss = subsets negs
                  projOr negs' t = tyOr t $ proj t1 t2 negs negs'
          proj :: Ty -> Ty -> [Prod] -> [Prod] -> Ty
          proj t1 t2 negs negs'
            | isEmpty t1' = emptyTy
            | isEmpty t2' = emptyTy
            | otherwise   = case idx of
                              First  -> t1'
                              Second -> t2'
            where t1' = tyAnd t1 (andNFsts negs')
                  t2' = tyAnd t2 (andNSnds (negs \\ negs'))
          andNFsts :: [Prod] -> Ty
          andNFsts ps = foldr andNotFst anyTy ps
            where andNotFst (Prod t1 _) t = tyAnd t (tyNot t1)
          andNSnds :: [Prod] -> Ty
          andNSnds ps = foldr andNotSnd anyTy ps
            where andNotSnd (Prod _ t2) t = tyAnd t (tyNot t2)

            

-- if t is a product, what type is returned
-- from it's first projection? If it is not
-- a product, return Nothing.
fstProj :: Ty -> Maybe Ty
fstProj = calcProj First

-- If t is a product, what type is returned
-- from it's second projection. If it is not
-- a product, return Nothing.
sndProj :: Ty -> Maybe Ty
sndProj = calcProj Second


-- given a type, if it is a function, return the collective
-- domain for the function type they represent, e.g.:
-- (⋂i∈I(⋃(Sₚ→Tₚ)∈Pᵢ Sₚ))
domTy :: Ty -> Maybe Ty
domTy t
  | not (isFun t) = Nothing
  | otherwise = Just dom
  where arrowsBDD = tyArrows t
        clauses :: [([Arrow] , [Arrow])]
        clauses = flattenBDD arrowsBDD
        clauseDoms :: [Ty]
        clauseDoms = map clauseDom clauses
        clauseDom :: ([Arrow] , [Arrow]) -> Ty
        clauseDom (pos, neg) = (foldr (\(Arrow t' _) t ->
                                         tyOr t t')
                                emptyTy
                                pos)
        dom = foldr tyAnd anyTy clauseDoms

-- If (1) fty is a function type and (2) argty is a subtype
-- of its domain, what is the return type for applying
-- an fty to an argty? If (1) and (2) are not both
-- satisfied, return Nothing.
rngTy :: Ty -> Ty -> Maybe Ty
rngTy funty argty =
  case (domTy funty) of
    (Just dom) | (subtype argty dom) -> Just res
    _ -> Nothing
  where ps = map fst $ flattenBDD $ tyArrows funty
        res = foldr rngOr emptyTy ps
        rngOr p t = tyOr t (calcRng p argty)


calcRng :: [Arrow] -> Ty -> Ty
calcRng p argty = foldr tyOr emptyTy ts
  where ps = nonEmptySubsets p
        ts = map getTy ps
        getTy :: [Arrow] -> Ty
        getTy pos
          | subtype argty compDom = emptyTy
          | otherwise = rng
          where compDom = (foldr (\(Arrow s1 _) t -> tyOr t s1)
                           emptyTy
                           (p \\ pos))
                rng = (foldr (\(Arrow _ s2) t -> tyAnd t s2)
                           anyTy
                           pos)


inTy :: Ty -> Ty -> Ty -> Maybe Ty
inTy funty arg out
  | not $ isFun funty = Nothing
  | otherwise = Just res
  where ps =  map fst $ flattenBDD $ tyArrows funty
        res = (foldr
                (\p t -> (tyOr t
                          (tyDiff
                            (calcInTy p arg out (not . isEmpty))
                            (calcInTy p arg out isEmpty))))
                emptyTy
                ps)


calcInTy :: [Arrow] -> Ty -> Ty -> (Ty -> Bool) -> Ty
calcInTy p arg out include = foldr tyOr emptyTy ps
  where ps = map go (nonEmptySubsets p)
        go :: [Arrow] -> Ty
        go p' = if (include rng)
                 then dom
                 else emptyTy
          where dom = foldr tyAnd arg (map arrowDom p')
                rng = foldr tyAnd out (map arrowRng p')
                arrowDom (Arrow t1 _) = t1 
                arrowRng (Arrow _ t2) = t2

  
