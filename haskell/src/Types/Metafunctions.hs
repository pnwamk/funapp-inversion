module Types.Metafunctions
  ( isFun
  , isProd
  , fstProj
  , sndProj
  , domTy
  , rngTy
  , inTy
  , cInTy
  ) where

import Types.Base
import Types.LazyBDD
import Types.Subtype

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
calcProj env select t
  | not (isProd env t) = Nothing
  | otherwise = Just (prodProj env select prods anyTy anyTy [])
    where (Ty _ prods _) = t

-- Is a BDD of prods equivalent to ∅?
prodProj :: Env -> (Ty -> Ty -> Ty) -> (BDD Prod) -> Ty -> Ty -> [Prod] -> Ty
prodProj env select bdd s1 s2 neg
  | (isEmpty env s1) = emptyTy
  | (isEmpty env s2) = emptyTy
  | otherwise =
    case bdd of
      (Node p@(Prod t1 t2) l m r) ->
        (tyOr env
         (prodProj env select l (tyAnd env s1 t1) (tyAnd env s2 t2) neg)
         (tyOr env
          (prodProj env select m s1 s2 neg)
          (prodProj env select r s1 s2 (p:neg))))
      Bot -> emptyTy
      Top -> aux select s1 s2 neg
  where aux :: (Ty -> Ty -> Ty) -> Ty -> Ty -> [Prod] -> Ty
        aux select s1 s2 neg
          | (isEmpty env s1) = emptyTy
          | (isEmpty env s2) = emptyTy
          | otherwise =
            case neg of
              [] -> select s1 s2
              (Prod t1 t2):neg' -> tyOr env res1 res2
                where s1'  = tyDiff env s1 t1
                      s2'  = tyDiff env s2 t2
                      res1 = (aux select s1' s2  neg')
                      res2 = (aux select s1  s2' neg')


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
  | otherwise = let (Ty _ _ arrows) = t in
      Just (aux anyTy emptyTy arrows)
      where aux ::  Ty -> Ty -> (BDD Arrow) -> Ty
            aux acc dom Top = tyAnd acc dom
            aux acc dom Bot = acc
            aux acc dom (Node (Arrow t _) l m r) = acc3
              where acc1 = aux acc (tyOr env dom t) l
                    acc2 = aux acc1 dom m
                    acc3 = aux acc2 dom r


-- If (1) fty is a function type and (2) argty is a subtype
-- of its domain, what is the return type for applying
-- an fty to an argty? If (1) and (2) are not both
-- satisfied, return Nothing.
rngTy :: Env -> Ty -> Ty -> Maybe Ty
rngTy env fty@(Ty _ _ arrows) argty =
  case (domTy env fty) of
    (Just dom) | (subtype env argty dom) -> Just $ loop arrows []
    _ -> Nothing
  where loop :: (BDD Arrow) -> [Arrow] -> Ty
        loop Bot p = emptyTy
        loop Top p = aux p argty anyTy
        loop (Node a@(Arrow s1 s2) l m r) p = tyOr env tl $ tyOr env tm tr
          where tl = if (overlap env s1 argty)
                     then loop l $ a:p
                     else loop l p
                tm = loop m p
                tr = loop r p
        aux :: [Arrow] -> Ty -> Ty -> Ty
        aux [] arg res
          | isEmpty env arg = emptyTy
          | otherwise = res
        aux ((Arrow s1 s2):p) arg res = tyOr res1 res2
          where res' = tyAnd env res s2
                arg' = tyDiff env arg s1
                res1 = if isEmpty env res'
                       then emptyTy
                       else aux p arg res'
                res2 = if isEmpty env arg'
                       then emptyTy
                       else aux p arg' res


inTy :: Env -> Ty -> Ty -> Ty -> Maybe Ty
inTy env fty@(Ty _ _ arrows) arg out =
  case (domTy env fty) of
    (Just dom) | (subtype env arg dom) -> Just $ input arrows []
    _ -> Nothing
  where input :: (BDD Arrow) -> [Arrow] -> Ty
        input Bot p = emptyTy
        input Top p = tyDiff env arg (aux arg out p)
        input (Node a l m r) p = tyOr env lty $ tyOr env mty rty
          where lty = input l $ a:p
                mty = input m p
                rty = input r p
        aux :: Ty -> Ty -> [Arrow] -> Ty
        aux dom rng []
          | (isEmpty env rng) = dom
          | otherwise     = emptyTy
        aux dom rng ((Arrow t1 t2):p) = tyOr neg1 neg2
          where dom' = (tyAnd env t1 dom)
                rng' = (tyAnd env t2 rng)
                neg1 = if isEmpty env dom'
                       then emptyTy
                       else if isEmpty env rng'
                            then dom'
                            else aux dom' rng' p
                neg2 = aux dom rng p

                  
-- conservative version, linear instead of exponential search
cInTy :: Env -> Ty -> Ty -> Ty -> Maybe Ty
cInTy env fty@(Ty _ _ arrows) arg out =
  case (domTy env fty) of
    (Just dom) | (subtype env arg dom) -> Just $ input arrows []
    _ -> Nothing
  where input :: (BDD Arrow) -> [Arrow] -> Ty
        input Bot p = emptyTy
        input Top p = tyDiff env arg (aux arg out p)
        input (Node a l m r) p = tyOr env lty $ tyOr env mty rty
          where lty = input l $ a:p
                mty = input m p
                rty = input r p
        aux :: Ty -> Ty -> [Arrow] -> Ty
        aux dom rng []
          | (isEmpty env rng) = dom
          | otherwise     = emptyTy
        aux dom rng ((Arrow t1 t2):p) = tyOr env neg1 neg2
          where dom' = (tyAnd env t1 dom)
                rng' = (tyAnd env t2 rng)
                neg1 = if isEmpty env dom'
                       then emptyTy
                       else if isEmpty env rng'
                            then dom'
                            else emptyTy
                neg2 = aux dom rng p

