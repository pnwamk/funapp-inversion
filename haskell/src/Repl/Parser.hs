module Repl.Parser ( parseCmd ) where

import Repl.Commands
import qualified Types.LazyBDD as BDD
import Types.NumericTower
import Text.Parsec.Prim (parserZero, parserFail)
import Text.ParserCombinators.Parsec hiding (spaces)
import System.Environment

parseCmd :: String -> Either String Cmd
parseCmd = run_parser cmdParser

cmdParser :: Parser Cmd 
cmdParser =
  try parseInhabited
  <|> try parseSubtype
  <|> try parseFstProj
  <|> try parseSndProj
  <|> try parseFunApp
  <|> try parseFunInv
  <|> try parseQuit
  <|> try parseHelp
  <|> parserFail "unrecognized command"

run_parser :: Parser a -> String -> Either String a
run_parser p str =  case parse p "" str of
  Left err -> Left $ "parse error at " ++ (show err)
  Right val  -> Right val  

spaces :: Parser ()
spaces = skipMany space

openParen :: Parser ()
openParen = do
  char '('
  spaces
  return ()

closeParen :: Parser ()
closeParen = do
  spaces
  char ')'
  return ()


parseInhabited :: Parser Cmd
parseInhabited = do
  openParen
  string "Inhabited"
  spaces
  [t] <- parseTyList
  closeParen
  return $ Inhabited t


parseSubtype :: Parser Cmd
parseSubtype = do
  openParen
  string "Subtype"
  spaces
  [t1,t2] <- parseTyList
  char ')'
  return $ Subtype t1 t2


parseFstProj :: Parser Cmd
parseFstProj = do
  openParen
  string "FstProj"
  spaces
  [t] <- parseTyList
  closeParen
  return $ FstProj t

parseSndProj :: Parser Cmd
parseSndProj = do
  openParen
  string "SndProj"
  spaces
  [t] <- parseTyList
  closeParen
  return $ SndProj t

parseFunApp :: Parser Cmd
parseFunApp = do
  openParen
  string "FunApp"
  spaces
  [t1,t2] <- parseTyList
  closeParen
  return $ FunApp t1 t2

parseFunInv :: Parser Cmd
parseFunInv = do
  openParen
  string "FunInv"
  spaces
  [t1,t2,t3] <- parseTyList
  closeParen
  return $ FunInv t1 t2 t3

parseQuit :: Parser Cmd
parseQuit = do
  openParen
  string "Quit"
  closeParen
  return Quit

parseHelp :: Parser Cmd
parseHelp = do
  char '('
  string "Help"
  char ')'
  return Help


parseTy :: Parser BDD.Ty
parseTy = parseTyName <|> do openParen
                             t <- parseCompoundTy
                             closeParen
                             return t

parseTyName :: Parser BDD.Ty
parseTyName = do 
  name <- many letter
  case (nameToTy name) of
    Just t -> return t
    Nothing -> parserZero

parseCompoundTy :: Parser BDD.Ty
parseCompoundTy = do
  t <- parseOr <|> parseAnd <|> parseNot <|> parseArrow <|> parseProd
  return t
  

parseTyList :: Parser [BDD.Ty]
parseTyList = sepBy parseTy space


parseOr :: Parser BDD.Ty
parseOr = do
  string "Or"
  spaces
  ts <- parseTyList
  return $ BDD.tyOr' ts

parseAnd :: Parser BDD.Ty
parseAnd = do
  string "And"
  spaces
  ts <- parseTyList
  return $ BDD.tyAnd' ts
  
parseNot :: Parser BDD.Ty
parseNot = do
  string "Not"
  spaces
  [t] <- parseTyList
  return $ BDD.tyNot t

parseArrow :: Parser BDD.Ty
parseArrow = do
  string "Fun"
  spaces
  [t1,t2] <- parseTyList
  return $ BDD.arrowTy t1 t2

parseProd :: Parser BDD.Ty
parseProd = do
  string "Pair"
  spaces
  [t1,t2] <- parseTyList
  return $ BDD.prodTy t1 t2
