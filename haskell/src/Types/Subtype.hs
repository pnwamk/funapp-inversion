module Types.Subtype
  ( overlap
  , subtype
  , equiv
  , isEmpty
  ) where

import           Types.LazyBDD
import           Data.Set (Set)
import qualified Data.Set as Set
import           Control.Applicative

-- Is this type equivalent to ∅?
isEmpty :: Ty -> Bool
isEmpty t = case mtTy t Set.empty of
              Just _  -> True
              Nothing -> False

type Seen = Set FiniteTy

-- internal isEmpty which tracks seen types
mtTy :: Ty -> Seen -> Maybe Seen
mtTy (Ty b ps as) seen
  | not $ b == emptyBase = Nothing
  | otherwise = mtProd ps anyTy anyTy [] seen
                >>=  mtArrow as emptyTy [] []
mtTy t@(TyNode fty b ps as) seen
  | Set.member fty seen  = Just seen
  | not $ b == emptyBase = Nothing
  | otherwise = 
      mtProd ps anyTy anyTy [] seen
      >>= mtArrow as emptyTy [] []
  

-- Is a BDD of prods equivalent to ∅?
mtProd :: (BDD Prod) -> Ty -> Ty -> [Prod] -> Seen -> Maybe Seen
mtProd (Node p@(Prod t1 t2) l m r) s1 s2 neg seen =
  mtProd l (tyAnd s1 t1) (tyAnd s2 t2) neg seen
  >>= mtProd m s1 s2 neg
  >>= mtProd r s1 s2 (p:neg)
mtProd Bot _ _ _ _ = Nothing
mtProd Top s1 s2 neg seen = mtTy s1 seen
                            <|> mtTy s2 seen
                            <|> go s1 s2 neg seen
  where go :: Ty -> Ty -> [Prod] -> Seen -> Maybe Seen
        go _ _ [] _ = Nothing
        go s1 s2 ((Prod t1 t2):neg) seen = do
          seen' <- ((mtTy diff1 seen) <|> (go diff1 s2 neg seen))
          ((mtTy diff2 seen') <|> (go s1 diff2 neg seen'))
          where diff1 = tyDiff s1 t1
                diff2 = tyDiff s2 t2

-- Is a BDD of arrows equivalent to ∅?
mtArrow :: (BDD Arrow) -> Ty -> [Arrow] -> [Arrow] -> Seen -> Maybe Seen
mtArrow (Node a@(Arrow s1 s2) l m r) dom pos neg seen =
  mtArrow l (tyOr s1 dom) (a:pos) neg seen
  >>= mtArrow m dom pos neg
  >>= mtArrow r dom pos (a:neg)
mtArrow Bot _ _ _ seen = Just seen
mtArrow Top dom pos [] seen = Nothing
mtArrow Top dom pos ((Arrow t1 t2):neg) seen = checkArrows neg
  where checkArrows :: [Arrow] -> Maybe Seen
        checkArrows [] = Nothing
        checkArrows ((Arrow t1 t2):rest) =
          (mtTy (tyDiff t1 dom) seen >>= arrowPhi t1 (tyNot t2) pos)
          <|> checkArrows rest


arrowPhi :: Ty -> Ty -> [Arrow] -> Seen -> Maybe Seen
arrowPhi t1 nt2 [] seen = mtTy t1 seen <|> mtTy nt2 seen
arrowPhi t1 nt2 ((Arrow s1 s2):arrows) seen = do
  seen' <- mtTy nt2' seen <|> arrowPhi t1 nt2' arrows seen
  mtTy t1' seen' <|> arrowPhi t1' nt2 arrows seen'
    where nt2' = tyAnd nt2 s2
          t1'  = tyDiff t1 s1

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
