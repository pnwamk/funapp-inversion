module Types.CompareOpTypes where

import Data.List
import qualified Types.Syntax as Stx
import Types.LazyBDD
import Types.Subtype
import Types.Metafunctions
import qualified Types.SyntacticOpTypes as Syn
import qualified Types.SemanticOpTypes as Sem


parseUnOpToSemantic :: [(Stx.Ty, Stx.Ty)] -> Ty
parseUnOpToSemantic [] = anyTy
parseUnOpToSemantic ((d,r):ts) =
  tyAnd (parseTy (Stx.Arrow d r)) $ parseUnOpToSemantic ts


mTyAnd :: Ty -> Maybe Ty -> Ty
mTyAnd t Nothing = t
mTyAnd t (Just t') = tyAnd t t'

-- return type using only the first applicable arrow
firstSynUnOpRng :: [(Stx.Ty, Stx.Ty)] -> Stx.Ty -> Maybe Ty
firstSynUnOpRng syn arg =
  case (find (\(d,r) ->
                 subtype (parseTy arg) (parseTy d))
         syn) of
    Nothing -> Nothing
    Just (d,r) -> Just (parseTy r)
    

-- return type using _all_ applicable arrows
allSynUnOpRng :: [(Stx.Ty, Stx.Ty)] -> Stx.Ty -> Maybe Ty
allSynUnOpRng [] argTy = Nothing
allSynUnOpRng ((s1,s2):rst) arg
  | (subtype (parseTy arg) (parseTy s1)) =
      Just (mTyAnd
            (parseTy s2)
            (allSynUnOpRng rst arg))
  | otherwise = allSynUnOpRng rst arg


-- verifies both function types work on the
-- same input types, and that the result for
-- fTy1 is a subtype of the result for fTy2
compareUnOpRes ::
  [(Stx.Ty, Stx.Ty)]
  -> ([(Stx.Ty, Stx.Ty)] -> Stx.Ty -> Maybe Ty)
  -> [(Stx.Ty, Stx.Ty)]
  -> ([(Stx.Ty, Stx.Ty)] -> Stx.Ty -> Maybe Ty)
  -> Stx.Ty
  -> Stx.Ty
  -> Bool
compareUnOpRes fTy1 rngTy1 fTy2 rngTy2 dom arg =
  case (res1, res2) of
    (Just t1, Just t2) -> subtype t1 t2
    (_,_) -> not (subtype (parseTy arg) (parseTy dom))
  where res1 = rngTy1 fTy1 arg
        res2 = rngTy2 fTy2 arg

-- identify duplicate cases in case-> if we were
-- to simply apply all possible arrows (returning
-- a list of the indices of the unnecessary arrows)
simplifyUnOp :: [(Stx.Ty, Stx.Ty)] -> [Integer]
simplifyUnOp orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2) =
          case (allSynUnOpRng (delete (t1,t2) orig) t1) of
            Just t -> (subtype t (parseTy t2))
            Nothing -> False

-- like simplifyUnOp
simplifyBinOp :: [(Stx.Ty, Stx.Ty, Stx.Ty)] -> [Integer]
simplifyBinOp orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2,r) =
          case (allSynBinOpRng (delete (t1,t2,r) orig) t1 t2) of
            Just t -> (subtype t (parseTy r))
            Nothing -> False





parseBinOpToSemantic :: [(Stx.Ty, Stx.Ty, Stx.Ty)] -> Ty
parseBinOpToSemantic [] = anyTy
parseBinOpToSemantic ((d1,d2,r):ts) =
  tyAnd (parseTy (Stx.Arrow (Stx.Prod d1 d2) r)) $ parseBinOpToSemantic ts


firstSynBinOpRng ::
  [(Stx.Ty, Stx.Ty, Stx.Ty)] ->
  Stx.Ty ->
  Stx.Ty ->
  Maybe Ty
firstSynBinOpRng syn arg1 arg2 =
  case (find (\(d1,d2,r) ->
                 (subtype (parseTy arg1) (parseTy d1))
                 && (subtype (parseTy arg2) (parseTy d2)))
         syn) of
    Nothing -> Nothing
    Just (d1,d2,r) -> Just (parseTy r)


allSynBinOpRng ::
  [(Stx.Ty, Stx.Ty, Stx.Ty)] ->
  Stx.Ty ->
  Stx.Ty ->
  Maybe Ty
allSynBinOpRng [] argTy1 argTy2 = Nothing
allSynBinOpRng ((d1,d2,r):rst) arg1 arg2
  | (subtype (parseTy arg1) (parseTy d1))
    && (subtype (parseTy arg2) (parseTy d2)) =
      Just (mTyAnd
            (parseTy r)
            (allSynBinOpRng rst arg1 arg2))
  | otherwise = allSynBinOpRng rst arg1 arg2



compareBinOpRes ::
  [(Stx.Ty, Stx.Ty, Stx.Ty)]
  -> ([(Stx.Ty, Stx.Ty, Stx.Ty)] -> Stx.Ty -> Stx.Ty -> Maybe Ty)
  -> [(Stx.Ty, Stx.Ty, Stx.Ty)]
  -> ([(Stx.Ty, Stx.Ty, Stx.Ty)] -> Stx.Ty -> Stx.Ty -> Maybe Ty)
  -> Stx.Ty
  -> Stx.Ty
  -> Stx.Ty
  -> Stx.Ty
  -> Bool
compareBinOpRes fTy1 rngTy1 fTy2 rngTy2 dom1 dom2 arg1 arg2 =
    case (res1, res2) of
      (Just t1, Just t2) -> subtype t1 t2
      (_,_) -> ((not (subtype (parseTy arg1) (parseTy dom1)))
                || (not (subtype (parseTy arg2) (parseTy dom2))))
  where res1 = rngTy1 fTy1 arg1 arg2
        res2 = rngTy2 fTy2 arg1 arg2



argType :: Stx.Ty -> Stx.Obj -> Stx.Prop -> Ty
argType d  _ Stx.FF = emptyTy
argType d _ Stx.TT = parseTy d
argType d o1 (Stx.IsA o2 t)
  | (o1 == o2) = tyAnd (parseTy d) (parseTy t)
  | otherwise = parseTy d
argType d o1 (Stx.Conj p1 p2) = tyAnd t1 t2
  where t1 = argType d o1 p1
        t2 = argType d o1 p2


firstSynCompOpProps ::
  [(Stx.Ty, Stx.Ty, Stx.Prop, Stx.Prop)] ->
  Stx.Ty ->
  Stx.Ty ->
  Maybe (Stx.Prop, Stx.Prop)
firstSynCompOpProps syn arg1 arg2 =
  case (find (\(d1,d2,pos,neg) ->
                 (subtype (parseTy arg1) (parseTy d1))
                 && (subtype (parseTy arg2) (parseTy d2)))
         syn) of
    Nothing -> Nothing
    Just (d1,d2,pos, neg) -> Just (pos,neg)


allSynCompOpProps ::
  [(Stx.Ty, Stx.Ty, Stx.Prop, Stx.Prop)] ->
  Stx.Ty ->
  Stx.Ty ->
  Maybe (Stx.Prop, Stx.Prop)
allSynCompOpProps [] argTy1 argTy2 = Nothing
allSynCompOpProps ((d1,d2,pos,neg):rst) arg1 arg2
  | (subtype (parseTy arg1) (parseTy d1))
    && (subtype (parseTy arg2) (parseTy d2)) =
    case (allSynCompOpProps rst arg1 arg2) of
      Just (pos',neg') -> Just (Stx.Conj pos pos', Stx.Conj neg neg') 
      Nothing -> Just (pos, neg)
  | otherwise = allSynCompOpProps rst arg1 arg2


-- Binary comparisons produce logical info about the first and second
-- argument. This function checks pos1 and neg1 are at least as strong
-- propositions as pos2 and neg2 (where pos are the props from getting
-- a truthy value back, and neg is the props from getting false back).
subProps :: Stx.Ty -> Stx.Ty -> Stx.Prop -> Stx.Prop -> Stx.Prop -> Stx.Prop -> Bool
subProps dom1 dom2 pos1 neg1 pos2 neg2 =
  (subtype
    (argType dom1 Stx.ArgZero pos1)
    (argType dom1 Stx.ArgZero pos2))
  && (subtype
       (argType dom1 Stx.ArgZero neg1)
       (argType dom1 Stx.ArgZero neg2))
  && (subtype
       (argType dom2 Stx.ArgOne pos1)
       (argType dom2 Stx.ArgOne pos2))
  && (subtype
       (argType dom2 Stx.ArgOne neg1)
       (argType dom2 Stx.ArgOne neg2))
  
compareCompOpRes ::
  [(Stx.Ty, Stx.Ty, Stx.Prop, Stx.Prop)]
  -> ([(Stx.Ty, Stx.Ty, Stx.Prop, Stx.Prop)] -> Stx.Ty -> Stx.Ty -> Maybe (Stx.Prop, Stx.Prop))
  -> [(Stx.Ty, Stx.Ty, Stx.Prop, Stx.Prop)]
  -> ([(Stx.Ty, Stx.Ty, Stx.Prop, Stx.Prop)] -> Stx.Ty -> Stx.Ty -> Maybe (Stx.Prop, Stx.Prop))
  -> Stx.Ty
  -> Stx.Ty
  -> Stx.Ty
  -> Stx.Ty
  -> Bool
compareCompOpRes fTy1 rngTy1 fTy2 rngTy2 dom1 dom2 arg1 arg2 =
  case (res1, res2) of
    (Just (pos1, neg1), Just (pos2, neg2)) ->
      subProps arg1 arg2 pos1 neg1 pos2 neg2
    (_,_) -> ((not (subtype (parseTy arg1) (parseTy dom1)))
              || (not (subtype (parseTy arg2) (parseTy dom2))))
  where res1 = rngTy1 fTy1 arg1 arg2
        res2 = rngTy2 fTy2 arg1 arg2



simplifyCompOp :: Stx.Ty -> Stx.Ty -> [(Stx.Ty, Stx.Ty, Stx.Prop, Stx.Prop)] -> [Integer]
simplifyCompOp dom1 dom2 orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2,pos,neg) =
          case (allSynCompOpProps (delete (t1,t2,pos,neg) orig) t1 t2) of
            Just (pos', neg') -> subProps t1 t2 pos' neg' pos neg
            Nothing -> False



compareBinPredRes ::
  (Ty -> Ty -> Ty -> Maybe Ty) ->
  Stx.Ty ->
  Stx.Ty ->
  Stx.Ty ->
  Stx.Ty ->
  [(Stx.Ty, Stx.Ty, Stx.Ty)] ->
  [(Stx.Ty, Stx.Ty, Stx.Prop, Stx.Prop)] ->
  Bool
compareBinPredRes inputTy dom1 dom2 arg1 arg2 sem syn =
    case (semPos1,semPos2,semNeg1,semNeg2,synRes) of
    (Just posTy1,
     Just posTy2,
     Just negTy1,
     Just negTy2,
     Just (posProp,negProp)) ->
      (subtype posTy1 (tyAnd argTy1 (argType dom1 Stx.ArgZero posProp)))
      && (subtype posTy2 (tyAnd argTy2 (argType dom2 Stx.ArgOne posProp)))
      && (subtype negTy1 (tyAnd argTy1 (argType dom1 Stx.ArgZero negProp)))
      && (subtype negTy2 (tyAnd argTy2 (argType dom2 Stx.ArgOne negProp)))
    (_,_,_,_,_) -> (not (subtype argTy1 domTy1))
                   || (not (subtype argTy2 domTy2))
  where domTy1 = parseTy dom1
        domTy2 = parseTy dom2
        argTy1 = parseTy arg1
        argTy2 = parseTy arg2
        argTy = prodTy argTy1 argTy2
        semTy = parseBinOpToSemantic sem
        semPos = inputTy semTy argTy $ parseTy (Stx.Not Stx.F)
        (semPos1,semPos2) =
          case semPos of
            Nothing -> (Nothing, Nothing)
            Just t -> (fstProj t, sndProj t)
        semNeg = inputTy semTy argTy $ parseTy Stx.F
        (semNeg1,semNeg2) =
          case semNeg of
            Nothing -> (Nothing, Nothing)
            Just t -> (fstProj t, sndProj t)
        synRes = case (find (\(d1,d2,pos,neg) ->
                               (subtype argTy1 (parseTy d1))
                               && (subtype argTy2 (parseTy d2)))
                        syn)
                 of
                   Nothing -> Nothing
                   Just (_,_,pos,neg) -> Just (pos,neg)
  

compareBinPredResIncomplete = compareBinPredRes inTy
