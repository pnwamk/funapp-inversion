module Types.CompareOpTypes where

import Data.List
import qualified Types.Syntax as Stx
import Types.LazyBDD
import Types.Subtype
import Types.Metafunctions
import qualified Types.SyntacticOpTypes as Syn
import qualified Types.SemanticOpTypes as Sem


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

-- return type using _all_ applicable arrows
semUnOpRng :: [(Stx.Ty, Stx.Ty)] -> Stx.Ty -> Maybe Ty
semUnOpRng ts arg = (rngTy
                     (parseUnOpToSemantic ts)
                     (parseTy arg))
  
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
    (Just t1, Just t2) -> (subtype t1 t2) &&
                          (((isEmpty t1) && (isEmpty t2)) || (overlap t1 t2))
    (_,_) -> not (subtype (parseTy arg) (parseTy dom))
  where res1 = rngTy1 fTy1 arg
        res2 = rngTy2 fTy2 arg

-- identify duplicate cases in case-> if we were
-- to simply apply all possible arrows (returning
-- a list of the indices of the unnecessary arrows)
simplifySynUnOp :: [(Stx.Ty, Stx.Ty)] -> [Integer]
simplifySynUnOp orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2) =
          case (allSynUnOpRng (delete (t1,t2) orig) t1) of
            Just t -> (subtype t (parseTy t2))
            Nothing -> False

-- like simplifyUnOp
simplifySynBinOp :: [(Stx.Ty, Stx.Ty, Stx.Ty)] -> [Integer]
simplifySynBinOp orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2,r) =
          case (allSynBinOpRng (delete (t1,t2,r) orig) t1 t2) of
            Just t -> (subtype t (parseTy r))
            Nothing -> False


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


-- return type using _all_ applicable arrows
semBinOpRng :: [(Stx.Ty, Stx.Ty, Stx.Ty)] -> Stx.Ty -> Stx.Ty -> Maybe Ty
semBinOpRng ts arg1 arg2 = (rngTy
                            (parseBinOpToSemantic ts)
                            (prodTy (parseTy arg1) (parseTy arg2)))


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
      (Just t1, Just t2) -> (subtype t1 t2) &&
                            (((isEmpty t1) && (isEmpty t2)) || (overlap t1 t2))
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


firstSynCompOpTypes ::
  [(Stx.Ty, Stx.Ty, Stx.Prop, Stx.Prop)] ->
  Stx.Ty ->
  Stx.Ty ->
  Maybe (Ty, Ty, Ty, Ty)
firstSynCompOpTypes syn arg1 arg2 =
  case (find (\(d1,d2,pos,neg) ->
                 (subtype (parseTy arg1) (parseTy d1))
                 && (subtype (parseTy arg2) (parseTy d2)))
         syn) of
    Nothing -> Nothing
    Just (d1,d2, pos, neg) -> Just ((argType arg1 Stx.ArgZero pos),
                                    (argType arg2 Stx.ArgOne pos),
                                    (argType arg1 Stx.ArgZero neg),
                                    (argType arg2 Stx.ArgOne neg))


allSynCompOpTypes ::
  [(Stx.Ty, Stx.Ty, Stx.Prop, Stx.Prop)] ->
  Stx.Ty ->
  Stx.Ty ->
  Maybe (Ty, Ty, Ty, Ty)
allSynCompOpTypes [] argTy1 argTy2 = Nothing
allSynCompOpTypes ((d1,d2,pos,neg):rst) arg1 arg2
  | (subtype (parseTy arg1) (parseTy d1))
    && (subtype (parseTy arg2) (parseTy d2)) =
    case (allSynCompOpTypes rst arg1 arg2) of
      Just (pos1, pos2, neg1, neg2) ->
        Just (tyAnd pos1 (argType arg1 Stx.ArgZero pos),
              tyAnd pos2 (argType arg2 Stx.ArgOne pos),
              tyAnd neg1 (argType arg1 Stx.ArgZero neg),
              tyAnd neg2 (argType arg2 Stx.ArgOne neg)) 
      Nothing -> Just ((argType arg1 Stx.ArgZero pos),
                       (argType arg2 Stx.ArgOne pos),
                       (argType arg1 Stx.ArgZero neg),
                       (argType arg2 Stx.ArgOne neg))
  | otherwise = allSynCompOpTypes rst arg1 arg2

  
compareCompOpRes ::
  a ->
  (a -> Stx.Ty -> Stx.Ty -> Maybe (Ty, Ty, Ty, Ty)) ->
  b ->
  (b -> Stx.Ty -> Stx.Ty -> Maybe (Ty, Ty, Ty, Ty)) ->
  Stx.Ty ->
  Stx.Ty ->
  Stx.Ty ->
  Stx.Ty ->
  Bool
compareCompOpRes fTy1 rngTy1 fTy2 rngTy2 dom1 dom2 arg1 arg2 =
  case (res1, res2) of
    (Just (pos1, pos2, neg1, neg2), Just (pos1', pos2', neg1', neg2')) ->
      (subtype pos1 pos1')
      && (subtype pos2 pos2')
      && (subtype neg1 neg1')
      && (subtype neg2 neg2')
    (_,_) -> ((not (subtype (parseTy arg1) (parseTy dom1)))
              || (not (subtype (parseTy arg2) (parseTy dom2))))
  where res1 = rngTy1 fTy1 arg1 arg2
        res2 = rngTy2 fTy2 arg1 arg2



simplifySynCompOp :: [(Stx.Ty, Stx.Ty, Stx.Prop, Stx.Prop)] -> [Integer]
simplifySynCompOp orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2,pos,neg) =
          case (allSynCompOpTypes (delete (t1,t2,pos,neg) orig) t1 t2) of
            Just (pos1, pos2, neg1, neg2) ->
              (subtype pos1 (argType t1 Stx.ArgZero pos))
              && (subtype pos2 (argType t2 Stx.ArgOne pos))
              && (subtype neg1 (argType t1 Stx.ArgZero neg))
              && (subtype neg2 (argType t2 Stx.ArgOne neg))
            Nothing -> False


parseUnOpToSemantic :: [(Stx.Ty, Stx.Ty)] -> Ty
parseUnOpToSemantic [] = anyTy
parseUnOpToSemantic ((d,r):ts) =
  tyAnd (parseTy (Stx.Arrow d r)) $ parseUnOpToSemantic ts


-- identify duplicate cases in case-> if we were
-- to use semantic subtyping-esq function application
simplifySemUnOp :: [(Stx.Ty, Stx.Ty)] -> [Integer]
simplifySemUnOp orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2) =
          case (rngTy
                (parseUnOpToSemantic (delete (t1,t2) orig))
                (parseTy t1)) of
            Just t -> (subtype t (parseTy t2))
            Nothing -> False


parseBinOpToSemantic :: [(Stx.Ty, Stx.Ty, Stx.Ty)] -> Ty
parseBinOpToSemantic [] = anyTy
parseBinOpToSemantic ((d1,d2,r):ts) =
  tyAnd (parseTy (Stx.Arrow (Stx.Prod d1 d2) r)) $ parseBinOpToSemantic ts


simplifySemBinOp :: [(Stx.Ty, Stx.Ty, Stx.Ty)] -> [Integer]
simplifySemBinOp orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2,r) =
          case (rngTy
                (parseBinOpToSemantic (delete (t1,t2,r) orig))
                (prodTy (parseTy t1) (parseTy t2))) of
            Just t -> (subtype t (parseTy r))
            Nothing -> False


semCompOpTypes ::
  (Ty -> Ty -> Ty -> Maybe Ty) ->
  [(Stx.Ty, Stx.Ty, Stx.Ty)] ->
  Stx.Ty ->
  Stx.Ty ->
  Maybe (Ty, Ty, Ty, Ty)
semCompOpTypes inputTy ts arg1 arg2 =
  case (pos1,pos2,neg1,neg2) of
    (Just posTy1,
     Just posTy2,
     Just negTy1,
     Just negTy2) -> Just (posTy1, posTy2, negTy1, negTy2)
    (_,_,_,_) -> Nothing
    where argTy1 = parseTy arg1
          argTy2 = parseTy arg2
          argTy = prodTy argTy1 argTy2
          semTy = parseBinOpToSemantic ts
          pos = inputTy semTy argTy $ parseTy (Stx.Not Stx.F)
          (pos1,pos2) =
            case pos of
              Nothing -> (Nothing, Nothing)
              Just t -> (fstProj t, sndProj t)
          neg = inputTy semTy argTy $ parseTy Stx.F
          (neg1,neg2) =
            case neg of
              Nothing -> (Nothing, Nothing)
              Just t -> (fstProj t, sndProj t)
