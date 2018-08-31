module Repl.Parse ( parseCmd ) where

-- this module defines tools for parsing user input
-- (or input from a Racket process) whose grammar
-- is s-expression based

import Types.LazyBDD
import Types.NumericTower
import Repl.Commands
import qualified Data.Map.Strict as Map
import Data.Char
import Control.Monad.Fail

-- what characters, aside from AlphaNums, are valid in symbols
allowedChars :: String
allowedChars = "-_+=~!@$%^&*"


-- reads the next identifier from the buffer, returning
-- (sym, rest) where sym is the parsed symbol and rest is
-- the input string after sym.
nextSym :: String -> Either String (String, String)
nextSym str = aux (skipSpace str) []
  where aux [] revSym
          | revSym == [] = Left $ "no characters to read"
          | otherwise = Right (reverse revSym, [])
        aux input@(c:rest) revSym
          -- if we hit a delimiter, return the symbol w/o consuming it
          | isSpace c || c == '(' || c == ')' = Right (reverse revSym, input)
          -- add a valid character to the symbol we're accumulating
          | isAlphaNum c || (any (== c) allowedChars) = aux rest (c:revSym)
          -- unrecognized symbol, error
          | otherwise = Left $
                        "invalid identifier symbol "
                        ++ [c] ++
                        if revSym == []
                        then ""
                        else "after reading " ++ (reverse revSym)



-- trims white space from the left of the given string
skipSpace :: String -> String
skipSpace [] = []
skipSpace str@(c:cs)
  | isSpace c = skipSpace cs
  | otherwise = str


parseCmd :: Env -> String -> Either String Cmd
parseCmd env [] = Left $ "no command to parse"
parseCmd env (c:body)
  | isSpace c = parseCmd env body
  | c == '(' = do
      (sym, rest) <- nextSym body
      case sym of
        "Inhabited" -> do
          (ts, rest') <- nextTyList env rest
          case ts of
            [t] -> Right $ Inhabited t
            _   -> Left $ "Inhabited command requires 1 argument, given " ++ (show ts)
        "Subtype" -> do
          (ts, rest') <- nextTyList env rest
          case ts of
            [t1, t2] -> Right $ Subtype t1 t2
            _   -> Left $  "Subtype command requires 2 arguments, given " ++ (show ts)
        "Project" -> do
          (i, rest') <- nextSym rest
          case i of
            "1" -> do
              (ts, _) <- nextTyList env rest'
              case ts of
                [t] -> Right $ FstProj t
                _ -> Left $ "Project expects one type after index, given " ++ (show ts)
            "2" -> do
              (ts, _) <- nextTyList env rest'
              case ts of
                [t] -> Right $ SndProj t
                _ -> Left $ "Project expects one type after index, given " ++ (show ts)
            _ -> Left $ "Project requires an index of 1 or 2, given " ++ i 
        "Apply" -> do
          (ts, rest') <- nextTyList env rest
          case ts of
            [t1, t2] -> Right $ FunApp t1 t2
            _   -> Left $ "Apply command requires 2 arguments, given " ++ (show ts)
        "Inversion" -> do
          (ts, rest') <- nextTyList env rest
          case ts of
            [t1, t2, t3] -> Right $ FunInv t1 t2 t3
            _   -> Left $ "Inversion command requires 3 arguments, given " ++ (show ts)
        "Let" -> do
          (name, rest') <- nextSym rest
          case resolve name env of
            Nothing -> do
              (ts, _) <- nextTyList env rest'
              case ts of
                [t] -> Right $ Let name t
                _ -> Left $ "expected one type after name in Let, found " ++ (show ts)
            Just t -> Left $ "cannot redefine type name " ++ name ++ "(i.e. it is already defined)"
        "LetRec" -> Left"LetRec not implemented yet"
        _ -> Left $ "invalid Command: " ++ sym

  
-- parses the next type, returning the type and rest of the
-- input string if successful
nextTy :: Env -> String -> Either String (Ty, String)
nextTy env [] = Left $ "no type to parse"
nextTy env input@(c:body)
  | isSpace c = nextTy env body
  | c == '(' = do
      (sym, rest) <-  nextSym body
      case sym of
        "Or" -> do
          (ts, rest') <- nextTyList env rest
          Right (foldr (tyOr env) emptyTy ts, rest')
        "And" -> do
          (ts, rest') <- nextTyList env rest
          Right (foldr (tyAnd env) anyTy ts, rest')
        "Not" -> do
          (ts, rest') <- nextTyList env rest
          case ts of
            [t] -> Right (tyNot env t, rest')
            _   -> Left $ "Not requires 1 argument, given " ++ (show ts)
        "Prod" -> do
          (ts, rest') <- nextTyList env rest
          case ts of
            [t1, t2] -> Right (prodTy t1 t2, rest')
            _   -> Left $ "Prod requires 2 arguments, given " ++ (show ts)
        "Arrow" -> do
          (ts, rest') <- nextTyList env rest
          case ts of
            [t1, t2] -> Right (arrowTy t1 t2, rest')
            _   -> Left $ "Arrow requires 2 arguments, given " ++ (show ts)
        _ -> Left $ "invalid type constructor: " ++ sym
  | c == ')' = Left $ "unexpected right parenthesis"
  | otherwise = do
      (sym, rest) <- nextSym input
      case resolve sym env of
        Nothing -> Left $ "unrecognized type name: " ++ sym
        Just t -> Right (t, rest)



nextTyList :: Env -> String -> Either String ([Ty], String)
nextTyList env input = aux input []
  where aux :: String -> [Ty] -> Either String ([Ty], String)
        aux [] ts = Left $ "end of input string, no closing parenthesis: " ++ input
        aux (')':rest) ts = Right (ts, rest)
        aux str@(c:rest) ts
          | isSpace c = aux rest ts
          | otherwise = do
              (t, rest') <- nextTy env str
              aux rest' (t:ts)
