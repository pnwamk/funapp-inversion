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
  -> [(Stx.Ty, Stx.Ty)]
  -> [(Stx.Ty, Stx.Ty)]
  -> Bool
compareUnOpRes arg sem syn =
  case (semRes, synRes) of
    (Just semResTy, Just synResTy) ->
      subtype semResTy synResTy
    (Nothing, Nothing) -> True
    (_,_) -> False
  where argTy = parseTy arg
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
  -> [(Stx.Ty, Stx.Ty, Stx.Ty)]
  -> [(Stx.Ty, Stx.Ty, Stx.Ty)]
  -> Bool
compareBinOpRes arg1 arg2 sem syn =
  case (semRes, synRes) of
    (Just semResTy, Just synResTy) ->
      subtype semResTy synResTy
    (Nothing, Nothing) -> True
    (_,_) -> False
  where argTy1 = parseTy arg1
        argTy2 = parseTy arg2
        semTy = parseBinOpToSemantic sem
        semRes = rngTy semTy $ prodTy argTy1 argTy2
        synRes = case (find (\(d1,d2,r) ->
                               (subtype argTy1 (parseTy d1))
                               && (subtype argTy2 (parseTy d2)))
                        syn)
                 of
                   Nothing -> Nothing
                   Just (d1,d2,r) -> Just (parseTy r)
