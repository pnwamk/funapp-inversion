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

import Types.LazyBDD
import Types.Subtype

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
  | not $ isProd t = Nothing
  | otherwise = Just $ prodProj idx prods anyTy anyTy []
    where (Ty _ prods _) = t

-- Is a BDD of prods equivalent to ∅?
prodProj :: Index -> (BDD Prod) -> Ty -> Ty -> [Prod] -> Ty
prodProj idx bdd s1 s2 neg
  | isEmpty s1 = emptyTy
  | isEmpty s2 = emptyTy
  | otherwise =
    case bdd of
      (Node p@(Prod t1 t2) l m r) ->
        let lty = prodProj idx l (tyAnd s1 t1) (tyAnd s2 t2) neg
            mty = prodProj idx m s1 s2 neg
            rty = prodProj idx r s1 s2 (p:neg)
        in tyOr lty $ tyOr mty rty
      Bot -> emptyTy
      Top -> go s1 s2 neg
  where go :: Ty -> Ty -> [Prod] -> Ty
        go s1 s2 neg
          | isEmpty s1 = emptyTy
          | isEmpty s2 = emptyTy
          | otherwise =
            case neg of
              [] -> case idx of
                      First  -> s1
                      Second -> s2
              (Prod t1 t2):neg' -> tyOr res1 res2
                where s1'  = tyDiff s1 t1
                      s2'  = tyDiff s2 t2
                      res1 = go s1' s2  neg'
                      res2 = go s1  s2' neg'


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
  | otherwise = let (Ty _ _ arrows) = t in
      Just (go anyTy emptyTy arrows)
      where go :: Ty -> Ty -> (BDD Arrow) -> Ty
            go acc dom Top = tyAnd acc dom
            go acc dom Bot = acc
            go acc dom (Node (Arrow t _) l m r) = acc3
              where acc1 = go acc (tyOr dom t) l
                    acc2 = go acc1 dom m
                    acc3 = go acc2 dom r


-- If (1) fty is a function type and (2) argty is a subtype
-- of its domain, what is the return type for applying
-- an fty to an argty? If (1) and (2) are not both
-- satisfied, return Nothing.
rngTy :: Ty -> Ty -> Maybe Ty
rngTy fty@(Ty _ _ arrows) argty =
  case (domTy fty) of
    (Just dom) | (subtype argty dom) -> Just $ loop arrows []
    _ -> Nothing
  where loop :: (BDD Arrow) -> [Arrow] -> Ty
        loop Bot p = emptyTy
        loop Top p = go p argty anyTy
        loop (Node a@(Arrow s1 s2) l m r) p = tyOr tl $ tyOr tm tr
          where tl = if (overlap s1 argty)
                     then loop l $ a:p
                     else loop l p
                tm = loop m p
                tr = loop r p
        go :: [Arrow] -> Ty -> Ty -> Ty
        go [] arg res
          | isEmpty arg = emptyTy
          | otherwise = res
        go ((Arrow s1 s2):p) arg res = tyOr res1 res2
          where res' = tyAnd res s2
                arg' = tyDiff arg s1
                res1 = if isEmpty res'
                       then emptyTy
                       else go p arg res'
                res2 = if isEmpty arg'
                       then emptyTy
                       else go p arg' res


inTy :: Ty -> Ty -> Ty -> Maybe Ty
inTy fty@(Ty _ _ arrows) arg out =
  case (domTy fty) of
    (Just dom) | (subtype arg dom) -> Just $ input arrows []
    _ -> Nothing
  where input :: (BDD Arrow) -> [Arrow] -> Ty
        input Bot p = emptyTy
        input Top p = tyDiff arg (go arg out p)
        input (Node a l m r) p = tyOr lty $ tyOr mty rty
          where lty = input l $ a:p
                mty = input m p
                rty = input r p
        go :: Ty -> Ty -> [Arrow] -> Ty
        go dom rng []
          | (isEmpty rng) = dom
          | otherwise     = emptyTy
        go dom rng ((Arrow t1 t2):p) = tyOr neg1 neg2
          where dom' = (tyAnd t1 dom)
                rng' = (tyAnd t2 rng)
                neg1 = if isEmpty dom'
                       then emptyTy
                       else if isEmpty rng'
                            then dom'
                            else go dom' rng' p
                neg2 = go dom rng p


-- conservative version, linear instead of exponential search
cInTy :: Ty -> Ty -> Ty -> Maybe Ty
cInTy fty@(Ty _ _ arrows) arg out =
  case (domTy fty) of
    (Just dom) | (subtype arg dom) -> Just $ input arrows []
    _ -> Nothing
  where input :: (BDD Arrow) -> [Arrow] -> Ty
        input Bot p = emptyTy
        input Top p = tyDiff arg (go arg out p)
        input (Node a l m r) p = tyOr lty $ tyOr mty rty
          where lty = input l $ a:p
                mty = input m p
                rty = input r p
        go :: Ty -> Ty -> [Arrow] -> Ty
        go dom rng []
          | (isEmpty rng) = dom
          | otherwise     = emptyTy
        go dom rng ((Arrow t1 t2):p) = tyOr neg1 neg2
          where dom' = (tyAnd t1 dom)
                rng' = (tyAnd t2 rng)
                neg1 = if isEmpty dom'
                       then emptyTy
                       else if isEmpty rng'
                            then dom'
                            else emptyTy
                neg2 = go dom rng p

