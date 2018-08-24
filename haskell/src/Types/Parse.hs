module Types.Parse
  ( nextSymbol
  , nextTy
  ) where

-- this module defines tools for parsing user input
-- (or input from a Racket process) whose grammar
-- is s-expression based


import Types.LazyBDD
import Types.NumericTower
import qualified Data.Map.Strict as Map
import Data.Char

revNameMap :: Map.Map String Ty
revNameMap = foldr (\(name, t) m -> Map.insert (reverse name) t m) Map.empty numericTypes

allowedSymbols :: String
allowedSymbols = "-_+=~!@$%^&*"

nextSymbol :: String -> (String, String)
nextSymbol str = (reverse sym, rst)
  where (sym,rst) = nextRevSymbol str

-- reads from the buffer, accumulating
-- non-whitespace or delimiter
nextRevSymbol :: String -> (String, String)
nextRevSymbol str = aux (skipSpace str) []
  where aux [] buff = (buff, [])
        aux str@(c:cs) buff
          | isSpace c || c == '(' || c == ')' = (buff, str)
          | isAlphaNum c || (any (== c) allowedSymbols) = aux cs (c:buff)
          | otherwise = error $ "invalid identifier symbol: " ++ [c]



-- read past whitespace
skipSpace :: String -> String
skipSpace [] = []
skipSpace str@(c:cs)
  | isSpace c = skipSpace cs
  | otherwise = str

nextTy :: String -> (Ty, String)
nextTy ('(':rst) =
  (case (nextRevSymbol rst) of
      ("rO",   rst') -> (case (nextTyList rst') of
                            (ts,rst'') -> (foldr tyOr emptyTy ts, rst''))
      ("dnA",  rst') -> (case (nextTyList rst') of
                           (ts, rst'') -> (foldr tyAnd anyTy ts, rst''))
      ("toN",  rst') -> (case (nextTyList rst') of
                           ([t], rst'') -> (tyNot t, rst'')
                           (ts,_) -> error $ "invalid arg for Not: " ++ (show ts))
      ("riaP", rst') -> (case (nextTyList rst') of
                            ([t1,t2],rst'') -> (prodTy t1 t2, rst'')
                            (ts,_) -> error $ "invalid args for Prod: " ++ (show ts))
      ("nuF",rst') -> (case (nextTyList rst') of
                           ([t1,t2], rst'') -> (arrowTy t1 t2, rst'')
                           (ts,_) -> error $ "invalid args for Arrow: " ++ (show ts))
      (h, rst') ->  error $ "invalid head pattern: " ++ h)
nextTy (')':rst)  = error "unexpected right parenthesis!"
nextTy str = case (Map.lookup sym revNameMap) of
               Nothing -> error $ (reverse sym) ++ " is not a type!"
               Just t -> (t, rst)
  where (sym, rst) = nextRevSymbol str        



nextTyList :: String -> ([Ty], String)
nextTyList origStr = aux origStr []
  where aux :: String -> [Ty] -> ([Ty], String)
        aux [] ts = error $ "end of input string, no closing paren: " ++ origStr
        aux (')':rst) ts = (ts, rst)
        aux str@(c:rst) ts
          | isSpace c = aux rst ts
          | otherwise = aux rst' (t:ts)
          where (t,rst') = nextTy str
