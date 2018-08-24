module Main where

import System.IO
import Types.Syntax
import System.Environment as Sys
import qualified Types.LazyBDD as BDD
import Types.Subtype
import Types.Metafunctions
import qualified Types.SyntacticOpTypes as Syn
import qualified Types.SyntacticOpTypesPlus as SynP
import qualified Types.SemanticOpTypes as Sem
import Types.CompareOpTypes
import Data.Foldable
import Types.Parse
import Data.Char


runComparisonTests :: IO ()
runComparisonTests = do
  compareSyntacticUnOps "Syntactic/Syntactic+"
  compareSyntacticBinOps "Syntactic/Syntactic+"
  compareSyntacticCompOps "Syntactic/Syntactic+"
  compareSemanticUnOps "Syntactic/Semantic"
  compareSemanticBinOps "Syntactic/Semantic"
  compareSemanticCompOps inTy "Syntactic/Semantic (inTy)"
  compareSemanticCompOps cInTy "Syntactic/Semantic (cInTy)"

readTy :: String -> Maybe BDD.Ty
readTy input = Just t
  where (t,_) = nextTy input

flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

-- if str contains an open paren, return
-- the remainder of the string,
-- otherwise return Nothing
containsOpenParen :: String -> Maybe String
containsOpenParen [] = Nothing
containsOpenParen ('(':rst) = Just rst
containsOpenParen (_:rst) = containsOpenParen rst

-- read the next sexpression from stdin
getSexp :: IO (Maybe String)
getSexp = do
  input <- getLine
  aux input [] 0
  where aux :: String -> String -> Int -> IO (Maybe String)
        aux (')':_) rbuff 0 = return Nothing
        aux (')':_) rbuff 1 = return $ Just (reverse (')':rbuff))
        aux (')':rst) rbuff depth = aux rst (')':rbuff) (depth-1)
        aux ('(':rst) rbuff depth = aux rst ('(':rbuff) (depth+1)
        aux (c:rst) [] 0
          | isSpace c = aux rst [] 0
          | otherwise = return Nothing
        aux (c:rst) rbuff depth = aux rst (c:rbuff) depth
        aux [] rbuff depth = do
          moreInput <- getLine
          aux moreInput (' ':rbuff) depth

readPrompt :: String -> IO (Maybe String)
readPrompt prompt = flushStr prompt >> getSexp

eval :: String -> [BDD.Ty] -> String
eval opName args = opName

parseExpr :: String -> Maybe (String, [BDD.Ty])
parseExpr input = Just ((show t), [])
  where (opName, rst) = (nextSymbol input)
        t = nextTy input

evalString :: String -> String
evalString expr = case (parseExpr expr) of
                    Nothing  -> "error parsing expression (see `help`, or use `quit` to abort)"
                    Just (op, args) -> eval op args

runRepl :: IO ()
runRepl = do
  result <- readPrompt "> "
  case result of
    Nothing -> do
      putStrLn "ERROR: invalid s-expression input! (Try `(help)` or `(quit)`)"
      runRepl
    Just "(quit)" -> putStrLn "Goodbye!"
    Just "(exit)" -> putStrLn "Goodbye!"
    Just "(help)" -> do
      putStrLn "Help not implemented yet..."
      runRepl
    Just str -> do
      putStrLn (evalString str)
      runRepl
    
main :: IO ()
main = do args <- Sys.getArgs
          case args of
               ["test"] -> runComparisonTests
               ["repl"] -> runRepl
               otherwise -> putStrLn "usage: numeric-sst [test|repl]"
  
