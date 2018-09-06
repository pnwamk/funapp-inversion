module Types.Subtype
  ( overlap
  , subtype
  , equiv
  , isEmpty
  ) where

import           Types.LazyBDD
import           Data.Set (Set)
import qualified Data.Set as Set

-- Is this type equivalent to ∅?
isEmpty :: Ty -> Bool
isEmpty t = case mtTy Set.empty t of
              Just _  -> True
              Nothing -> False

type Seen = Set FiniteTy

-- internal isEmpty which tracks seen types
mtTy :: Ty -> Seen -> Maybe Seen
mtTy (Ty (Base True 0) ps as) seen =
  isEmptyProd ps anyTy anyTy [] seen
  >>=  isEmptyArrow as emptyTy [] []
mtTy seen (Ty _ _ _) = Nothing
mtTy seen t@(TyNode fty b ps as)
  | Set.member seen fty  = Just seen
  | not $ b == emptyBase = Nothing
  | otherise = 
      isEmptyProd ps anyTy anyTy [] seen
      >>= isEmptyArrow as emptyTy [] []
  

-- BOOKMARK, making this monadic in Maybe Seen
-- Is a BDD of prods equivalent to ∅?
isEmptyProd :: (BDD Prod) -> Ty -> Ty -> [Prod] -> Seen -> Maybe Seen
isEmptyProd (Node p@(Prod t1 t2) l m r) s1 s2 neg seen =
  isEmptyProd l (tyAnd s1 t1) (tyAnd s2 t2) neg seen
  >>= isEmptyProd seen m s1 s2 neg
  >>= isEmptyProd seen r s1 s2 (p:neg)
isEmptyProd Bot _ _ _ _ = True
isEmptyProd Top s1 s2 neg seen = isEmpty seen s1
                                 <|> isEmpty seen s2
                                 <|> go s1 s2 neg
  where go :: Ty -> Ty -> [Prod] -> Bool
        go s1 s2 [] = False
        go s1 s2 ((Prod t1 t2):neg) = lEmpty && rEmpty
          where lEmpty = (isEmpty diff1) <|> (go diff1 s2 neg)
                diff1 = tyDiff s1 t1
                rEmpty = ((isEmpty diff2) <|> (go s1 diff2 neg))
                diff2 = tyDiff s2 t2

-- Is a BDD of arrows equivalent to ∅?
isEmptyArrow :: Seen -> (BDD Arrow) -> Ty -> [Arrow] -> [Arrow] -> Maybe Seen
isEmptyArrow (Node a@(Arrow s1 s2) l m r) dom pos neg =
  (isEmptyArrow l (tyOr s1 dom) (a:pos) neg)
  && (isEmptyArrow m dom pos neg)
  && (isEmptyArrow r dom pos (a:neg))
isEmptyArrow Bot _ _ _ = True
isEmptyArrow Top dom pos neg = any (emptyArrow dom pos) neg
  where emptyArrow :: Ty -> [Arrow] -> Arrow -> Bool
        emptyArrow allDom allPos (Arrow t1 t2) =
          (subtype t1 allDom) && go t1 (tyNot t2) allPos
          where go :: Ty -> Ty -> [Arrow] -> Bool
                go t1 nt2 [] = (isEmpty t1) || (isEmpty nt2)
                go t1 nt2 ((Arrow s1 s2):pos) =
                  (((isEmpty nt2') || (go t1 nt2' pos))
                   &&
                   ((isEmpty t1') || (go t1' nt2 pos)))
                  where nt2' = tyAnd nt2 s2
                        t1'  = tyDiff t1 s1


-- is [[t1]] ∩ [[t2]] ≠ ∅
overlap :: Ty -> Ty -> Bool
overlap t1 t2 = not (isEmpty (tyAnd t1 t2))


-- Is t1 a subtype of t2
-- i.e. [[t1]] ⊆ [[t2]]
subtype :: Ty -> Ty -> Bool
subtype t1 t2 = isEmpty (tyDiff t1 t2)


-- Is t1 equivalent to t2
-- i.e. [[t1]] ⊆ [[t2]] and [[t1]] ⊇ [[t2]]
equiv :: Ty -> Ty -> Bool
equiv t1 t2 = subtype t1 t2 && subtype t2 t1
