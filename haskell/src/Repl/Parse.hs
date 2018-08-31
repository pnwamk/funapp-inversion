module Repl.Parse ( parseCmd , parseTy ) where

-- this module defines tools for parsing user input
-- (or input from a Racket process) whose grammar
-- is s-expression based

import qualified Types.LazyBDD as BDD
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
parseSym :: String -> Either String (String, String)
parseSym str = aux (skipSpace str) []
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


parseCmd :: BDD.Env -> String -> Either String Cmd
parseCmd env [] = Left $ "no command to parse"
parseCmd env (c:body)
  | isSpace c = parseCmd env body
  | c == '(' = do
      (sym, rest) <- parseSym body
      case sym of
        "Inhabited" -> do
          (ts, rest') <- parseTyList env rest
          case ts of
            [t] -> Right $ Inhabited t
            _   -> Left $ "Inhabited command requires 1 argument, given " ++ (show ts)
        "Subtype" -> do
          (ts, rest') <- parseTyList env rest
          case ts of
            [t1, t2] -> Right $ Subtype t1 t2
            _   -> Left $  "Subtype command requires 2 arguments, given " ++ (show ts)
        "Project" -> do
          (i, rest') <- parseSym rest
          case i of
            "1" -> do
              (ts, _) <- parseTyList env rest'
              case ts of
                [t] -> Right $ FstProj t
                _ -> Left $ "Project expects one type after index, given " ++ (show ts)
            "2" -> do
              (ts, _) <- parseTyList env rest'
              case ts of
                [t] -> Right $ SndProj t
                _ -> Left $ "Project expects one type after index, given " ++ (show ts)
            _ -> Left $ "Project requires an index of 1 or 2, given " ++ i 
        "Apply" -> do
          (ts, rest') <- parseTyList env rest
          case ts of
            [t1, t2] -> Right $ FunApp t1 t2
            _   -> Left $ "Apply command requires 2 arguments, given " ++ (show ts)
        "Inversion" -> do
          (ts, rest') <- parseTyList env rest
          case ts of
            [t1, t2, t3] -> Right $ FunInv t1 t2 t3
            _   -> Left $ "Inversion command requires 3 arguments, given " ++ (show ts)
        "Let" -> do
          (name, rest') <- parseSym rest
          case BDD.resolve name env of
            Nothing -> do
              (ts, _) <- parseTyList env rest'
              case ts of
                [t] -> Right $ Let name t
                _ -> Left $ "expected one type after name in Let, found " ++ (show ts)
            Just t -> Left $ "cannot redefine type name " ++ name ++ "(i.e. it is already defined)"
        "LetRec" -> Left"LetRec not implemented yet"
        _ -> Left $ "invalid Command: " ++ sym

  
-- parses the next type, returning the type and rest of the
-- input string if successful
parseTy :: BDD.Env -> String -> Either String (BDD.Ty, String)
parseTy env [] = Left $ "no type to parse"
parseTy env input@(c:body)
  | isSpace c = parseTy env body
  | c == '(' = do
      (sym, rest) <-  parseSym body
      case sym of
        "Or" -> do
          (ts, rest') <- parseTyList env rest
          Right (foldr (BDD.tyOr env) BDD.emptyTy ts, rest')
        "And" -> do
          (ts, rest') <- parseTyList env rest
          Right (foldr (BDD.tyAnd env) BDD.anyTy ts, rest')
        "Not" -> do
          (ts, rest') <- parseTyList env rest
          case ts of
            [t] -> Right (BDD.tyNot env t, rest')
            _   -> Left $ "Not requires 1 argument, given " ++ (show ts)
        "Prod" -> do
          (ts, rest') <- parseTyList env rest
          case ts of
            [t1, t2] -> Right (BDD.prodTy t1 t2, rest')
            _   -> Left $ "Prod requires 2 arguments, given " ++ (show ts)
        "Arrow" -> do
          (ts, rest') <- parseTyList env rest
          case ts of
            [t1, t2] -> Right (BDD.arrowTy t1 t2, rest')
            _   -> Left $ "Arrow requires 2 arguments, given " ++ (show ts)
        _ -> Left $ "invalid type constructor: " ++ sym
  | c == ')' = Left $ "unexpected right parenthesis"
  | otherwise = do
      (sym, rest) <- parseSym input
      case BDD.resolve sym env of
        Nothing -> Left $ "unrecognized type name: " ++ sym
        Just t -> Right (t, rest)



parseTyList :: BDD.Env -> String -> Either String ([BDD.Ty], String)
parseTyList env input = aux input []
  where aux :: String -> [BDD.Ty] -> Either String ([BDD.Ty], String)
        aux [] ts = Left $ "end of input string, no closing parenthesis: " ++ input
        aux (')':rest) ts = Right (reverse ts, rest)
        aux str@(c:rest) ts
          | isSpace c = aux rest ts
          | otherwise = do
              (t, rest') <- parseTy env str
              aux rest' (t:ts)
