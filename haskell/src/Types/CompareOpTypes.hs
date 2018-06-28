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


compareUnOpRes ::
  Stx.Ty
  -> Stx.Ty
  -> [(Stx.Ty, Stx.Ty)]
  -> [(Stx.Ty, Stx.Ty)]
  -> Bool
compareUnOpRes dom arg sem syn =
  case (semRes, synRes) of
    (Just semResTy, Just synResTy) ->
      subtype semResTy synResTy
    (Nothing, Nothing) -> False
    (_,_) -> not (subtype argTy domTy)
  where domTy = parseTy dom
        argTy = parseTy arg
        semTy = parseUnOpToSemantic sem
        semRes = rngTy semTy argTy
        synRes = case (find (\(d,r) ->
                               subtype argTy (parseTy d))
                        syn)
                 of
                   Nothing -> Nothing
                   Just (d,r) -> Just (parseTy r)
  

parseBinOpToSemantic :: [(Stx.Ty, Stx.Ty, Stx.Ty)] -> Ty
parseBinOpToSemantic [] = anyTy
parseBinOpToSemantic ((d1,d2,r):ts) =
  tyAnd (parseTy (Stx.Arrow (Stx.Prod d1 d2) r)) $ parseBinOpToSemantic ts


compareBinOpRes ::
  Stx.Ty
  -> Stx.Ty
  -> Stx.Ty
  -> Stx.Ty
  -> [(Stx.Ty, Stx.Ty, Stx.Ty)]
  -> [(Stx.Ty, Stx.Ty, Stx.Ty)]
  -> Bool
compareBinOpRes dom1 dom2 arg1 arg2 sem syn =
  case (semRes, synRes) of
    (Just semResTy, Just synResTy) ->
      subtype semResTy synResTy
    (_,_) -> (not (subtype argTy1 domTy1))
             || (not (subtype argTy2 domTy2)) 
  where domTy1 = parseTy dom1
        domTy2 = parseTy dom2
        argTy1 = parseTy arg1
        argTy2 = parseTy arg2
        semTy = parseBinOpToSemantic sem
        semRes = rngTy semTy $ prodTy argTy1 argTy2
        synRes = case (find (\(d1,d2,r) ->
                               (subtype argTy1 (parseTy d1))
                               && (subtype argTy2 (parseTy d2)))
                        syn)
                 of
                   Nothing -> Nothing
                   Just (_,_,r) -> Just (parseTy r)


argType :: Stx.Ty -> Stx.Obj -> Stx.Prop -> Ty
argType d  _ Stx.FF = emptyTy
argType d _ Stx.TT = parseTy d
argType d o1 (Stx.IsA o2 t)
  | (o1 == o2) = parseTy t
  | otherwise = parseTy d
argType d o1 (Stx.Conj p1 p2) = tyAnd t1 t2
  where t1 = argType d o1 p1
        t2 = argType d o1 p2


compareBinPredRes ::
  Stx.Ty
  -> Stx.Ty
  -> Stx.Ty
  -> Stx.Ty
  -> [(Stx.Ty, Stx.Ty, Stx.Ty)]
  -> [(Stx.Ty, Stx.Ty, Stx.Prop, Stx.Prop)]
  -> Bool
compareBinPredRes dom1 dom2 arg1 arg2 sem syn =
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
        semPos = inTy semTy argTy $ parseTy (Stx.Not Stx.F)
        (semPos1,semPos2) =
          case semPos of
            Nothing -> (Nothing, Nothing)
            Just t -> (fstProj t, sndProj t)
        semNeg = inTy semTy argTy $ parseTy Stx.F
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
  
