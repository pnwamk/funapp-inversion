module Types.NMetafunctions
  ( isFun
  , isProd
  , fstProj
  , sndProj
  , domTy
  , rngTy
  , inTy
  ) where

import Types.Base
import Types.LazyBDD
import Types.NSubtype (flattenProds, flattenBDD)
import Types.Subtype
import Data.List
import Common.SetOps

-- Is this a function type?
isFun :: Env -> Ty -> Bool
isFun env t = subtype env t anyArrowTy

-- Is this a function type?
isProd :: Env -> Ty -> Bool
isProd env t = subtype env t anyProdTy


-- Calculates the projection type for a given type
-- i.e. given (\(Prod t _) -> t) (prodTy T F)
--      it should produce T, also
--      given (\(Prod _ t) -> t) (prodTy T F)
--      it should produce F.
-- Works on complex types that are <: Any × Any.
-- Equivalent to ⋃i∈I(⋃N'⊆Nᵢ(⋂p∈Pᵢ Sₚ & ⋂n∈N' ¬Sₙ))
-- where the original product type is
-- ⋃i∈I(̱ ⋂p∈Pᵢ (Sₚ , Tₚ)  &  ⋂n∈Nᵢ  ¬(Sₙ , Tₙ) )
calcProj :: Env -> (Ty -> Ty -> Ty) -> Ty -> Maybe Ty
calcProj env select t@(Ty _ ps _)
  | not (isProd env t) = Nothing
  | otherwise = Just $ foldl (tyOr env) emptyTy clauses
    where clauses :: [Ty]
          clauses = map clauseProj $ flattenProds env ps
          clauseProj :: (Prod, [Prod]) -> Ty
          clauseProj ((Prod t1 t2), negs) = foldr projOr emptyTy negss
            where negss = subsets negs
                  projOr negs' t = tyOr env t $ proj t1 t2 negs negs'
          proj :: Ty -> Ty -> [Prod] -> [Prod] -> Ty
          proj t1 t2 negs negs'
            | isEmpty env t1' = emptyTy
            | isEmpty env t2' = emptyTy
            | otherwise   = select t1' t2'
            where t1' = tyAnd env t1 (andNFsts negs')
                  t2' = tyAnd env t2 (andNSnds (negs \\ negs'))
          andNFsts :: [Prod] -> Ty
          andNFsts ps = foldr andNotFst anyTy ps
            where andNotFst (Prod t1 _) t = tyAnd env t (tyNot env t1)
          andNSnds :: [Prod] -> Ty
          andNSnds ps = foldr andNotSnd anyTy ps
            where andNotSnd (Prod _ t2) t = tyAnd env t (tyNot env t2)

            

-- if t is a product, what type is returned
-- from it's first projection? If it is not
-- a product, return Nothing.
fstProj :: Env -> Ty -> Maybe Ty
fstProj env t = calcProj env (\t1 t2 -> t1) t

-- If t is a product, what type is returned
-- from it's second projection. If it is not
-- a product, return Nothing.
sndProj :: Env -> Ty -> Maybe Ty
sndProj env t = calcProj env (\t1 t2 -> t2) t


-- given a type, if it is a function, return the collective
-- domain for the function type they represent, e.g.:
-- (⋂i∈I(⋃(Sₚ→Tₚ)∈Pᵢ Sₚ))
domTy :: Env -> Ty -> Maybe Ty
domTy env t
  | not (isFun env t) = Nothing
  | otherwise = Just dom
  where (Ty _ _ arrowsBDD) = t
        clauses :: [([Arrow] , [Arrow])]
        clauses = flattenBDD arrowsBDD
        clauseDoms :: [Ty]
        clauseDoms = map clauseDom clauses
        clauseDom :: ([Arrow] , [Arrow]) -> Ty
        clauseDom (pos, neg) = (foldr (\(Arrow t' _) t ->
                                         tyOr env t t')
                                emptyTy
                                pos)
        dom = foldr (tyAnd env) anyTy clauseDoms

-- If (1) fty is a function type and (2) argty is a subtype
-- of its domain, what is the return type for applying
-- an fty to an argty? If (1) and (2) are not both
-- satisfied, return Nothing.
rngTy :: Env -> Ty -> Ty -> Maybe Ty
rngTy env fty@(Ty _ _ arrows) argty =
  case (domTy env fty) of
    (Just dom) | (subtype env argty dom) -> Just res
    _ -> Nothing
  where ps = map fst (flattenBDD arrows)
        res = foldr rngOr emptyTy ps
        rngOr p t = tyOr env t (calcRng env p argty)


calcRng :: Env -> [Arrow] -> Ty -> Ty
calcRng env p argty = foldr (tyOr env) emptyTy ts
  where ps = nonEmptySubsets p
        ts = map getTy ps
        getTy :: [Arrow] -> Ty
        getTy pos
          | subtype env argty compDom = emptyTy
          | otherwise = rng
          where compDom = (foldr (\(Arrow s1 _) t -> tyOr env t s1)
                           emptyTy
                           (p \\ pos))
                rng = (foldr (\(Arrow _ s2) t -> tyAnd env t s2)
                           anyTy
                           pos)


inTy :: Env -> Ty -> Ty -> Ty -> Maybe Ty
inTy env fty@(Ty _ _ arrows) arg out
  | not $ isFun env fty = Nothing
  | otherwise = Just res
  where ps =  map fst (flattenBDD arrows)
        res = (foldr
                (\p t -> (tyOr env t
                          (tyDiff env
                            (calcInTy env p arg out (not . (isEmpty env)))
                            (calcInTy env p arg out (isEmpty env)))))
                emptyTy
                ps)


calcInTy :: Env -> [Arrow] -> Ty -> Ty -> (Ty -> Bool) -> Ty
calcInTy env p arg out include = foldr (tyOr env) emptyTy (map aux (nonEmptySubsets p))
  where aux :: [Arrow] -> Ty
        aux p' = if (include rng)
                 then dom
                 else emptyTy
          where dom = foldr (tyAnd env) arg (map arrowDom p')
                rng = foldr (tyAnd env) out (map arrowRng p')
                arrowDom (Arrow t1 _) = t1 
                arrowRng (Arrow _ t2) = t2

  
