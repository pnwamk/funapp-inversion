module Repl.Parser ( parseCmd ) where

import Repl.Commands
import qualified Types.LazyBDD as BDD
import Types.NumericTower
import Text.Parsec.Prim (parserZero, parserFail)
import Text.ParserCombinators.Parsec hiding (spaces)
import System.Environment

run_parser :: Parser a -> String -> Either String a
run_parser p str =  case parse p "" str of
  Left err -> Left $ "parse error at " ++ (show err)
  Right val  -> Right val  


parseCmd :: String -> Either String Cmd
parseCmd = run_parser cmdParser

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


cmdParser :: Parser Cmd 
cmdParser = do
  openParen
  cmd <- many letter
  case cmd of
    "Inhabited" -> do
      spaces
      t <- parseTy
      closeParen
      return $ Inhabited t
    "Subtype" -> do
      spaces
      t1 <- parseTy
      spaces
      t2 <- parseTy
      closeParen
      return $ Subtype t1 t2
    "Project" -> do
      i <- char '1' <|> char '2' <?> "a 1 or 2"
      spaces
      t <- parseTy
      closeParen
      case i of
        '1' -> return $ FstProj t
        '2' -> return $ SndProj t
    "Apply" -> do
      spaces
      t1 <- parseTy
      spaces
      t2 <- parseTy
      closeParen
      return $ FunApp t1 t2
    "Inversion" -> do
      spaces
      t1 <- parseTy
      spaces
      t2 <- parseTy
      spaces
      t3 <- parseTy
      closeParen
      return $ FunInv t1 t2 t3
    "Quit" -> do
      closeParen
      return Quit
    "Help" -> do
      closeParen
      return Help
    _ -> parserFail $ "'" ++ cmd ++ "' is not a valid command!"

parseTy :: Parser BDD.Ty
parseTy = parseTyName <|> parseCompoundTy

parseTyName :: Parser BDD.Ty
parseTyName = do
  name <- many letter
  case (nameToTy name) of
    Just t -> return t
    Nothing -> parserFail $ "'" ++ name ++ "' is not a valid type name!"

parseTyList :: Parser [BDD.Ty]
parseTyList = do
  spaces
  t <- parseTy
  sepBy parseTy space


parseCompoundTy :: Parser BDD.Ty
parseCompoundTy = do
  openParen
  constructor <- many letter
  case constructor of
    "Or" -> do
      ts <- parseTyList
      closeParen
      return $ BDD.tyOr' ts
    "And" -> do
      ts <- parseTyList
      closeParen
      return $ BDD.tyAnd' ts
    "Not" -> do
      spaces
      t <- parseTy
      closeParen
      return $ BDD.tyNot t
    "Arrow" -> do
      spaces
      t1 <- parseTy
      spaces
      t2 <- parseTy
      closeParen
      return $ BDD.arrowTy t1 t2
    "Prod" -> do
      spaces
      t1 <- parseTy
      spaces
      t2 <- parseTy
      closeParen
      return $ BDD.prodTy t1 t2
    _ -> parserFail $ "'" ++ constructor ++ "' is not a valid type constructor"
  
