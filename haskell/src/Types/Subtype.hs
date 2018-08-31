module Types.Subtype
  ( overlap
  , subtype
  , equiv
  , isEmpty
  ) where


import Types.Base
import Types.LazyBDD

-- Is this type equivalent to ∅?
isEmpty :: Env -> Ty -> Bool
isEmpty env (Ty b ps as) =
  (b == emptyBase)
  && (isEmptyProd env ps anyTy anyTy [])
  && (isEmptyArrow env as emptyTy [] [])


-- Is a BDD of prods equivalent to ∅?
isEmptyProd :: Env -> (BDD Prod) -> Ty -> Ty -> [Prod] -> Bool
isEmptyProd env (Node p@(Prod t1 t2) l m r) s1 s2 neg =
  (isEmptyProd env l (tyAnd env s1 t1) (tyAnd env s2 t2) neg)
  && (isEmptyProd env m s1 s2 neg)
  && (isEmptyProd env r s1 s2 (p:neg))
isEmptyProd env Bot _ _ _ = True
isEmptyProd env Top s1 s2 neg = ((isEmpty env s1)
                                 || (isEmpty env s2)
                                 || (aux s1 s2 neg))
  where aux :: Ty -> Ty -> [Prod] -> Bool
        aux s1 s2 [] = False
        aux s1 s2 ((Prod t1 t2):neg) = lEmpty && rEmpty
          where lEmpty = ((isEmpty env diff1) || (aux diff1 s2 neg))
                diff1 = (tyDiff env s1 t1)
                rEmpty = ((isEmpty env diff2) || (aux s1 diff2 neg))
                diff2 = (tyDiff env s2 t2)

-- Is a BDD of arrows equivalent to ∅?
isEmptyArrow :: Env -> (BDD Arrow) -> Ty -> [Arrow] -> [Arrow] -> Bool
isEmptyArrow env (Node a@(Arrow s1 s2) l m r) dom pos neg =
  (isEmptyArrow env l (tyOr env s1 dom) (a:pos) neg)
  && (isEmptyArrow env m dom pos neg)
  && (isEmptyArrow env r dom pos (a:neg))
isEmptyArrow env Bot _ _ _ = True
isEmptyArrow env Top dom pos neg = any (emptyArrow dom pos) neg
  where emptyArrow :: Ty -> [Arrow] -> Arrow -> Bool
        emptyArrow allDom allPos (Arrow t1 t2) =
          (subtype env t1 allDom) && aux t1 (tyNot env t2) allPos
          where aux :: Ty -> Ty -> [Arrow] -> Bool
                aux t1 nt2 [] = (isEmpty env t1) || (isEmpty env nt2)
                aux t1 nt2 ((Arrow s1 s2):pos) =
                  (((isEmpty env nt2') || (aux t1 nt2' pos))
                   &&
                   ((isEmpty env t1') || (aux t1' nt2 pos)))
                  where nt2' = (tyAnd env nt2 s2)
                        t1'  = (tyDiff env t1 s1)


-- is [[t1]] ∩ [[t2]] ≠ ∅
overlap :: Env -> Ty -> Ty -> Bool
overlap env t1 t2 = not (isEmpty env (tyAnd env t1 t2))


-- Is t1 a subtype of t2
-- i.e. [[t1]] ⊆ [[t2]]
subtype :: Env -> Ty -> Ty -> Bool
subtype env t1 t2 = isEmpty env (tyDiff env t1 t2)


-- Is t1 equivalent to t2
-- i.e. [[t1]] ⊆ [[t2]] and [[t1]] ⊇ [[t2]]
equiv :: Env -> Ty -> Ty -> Bool
equiv env t1 t2 = subtype env t1 t2 && subtype env t2 t1
