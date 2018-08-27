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
import Repl.Parser
import Repl.Commands


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

parseExpr :: String -> Maybe (String, [BDD.Ty])
parseExpr input = Just ((show t), [])
  where (opName, rst) = (nextSymbol input)
        t = nextTy input

evalString :: String -> String
evalString expr =
  case (parseCmd expr) of
    Left msg  -> "(ERROR parsing expression, "
                 ++ "see `(Help)`, or use `(Quit)` to abort.\n"
                 ++ "  Error: " ++ msg ++ ")"
    Right cmd -> execCmd cmd

runRepl :: String -> IO ()
runRepl userPrompt = do
  result <- readPrompt userPrompt
  case result of
    Nothing -> do
      putStrLn "(ERROR: invalid s-expression input! Try `(Help)` or `(Quit)`)"
      runRepl userPrompt
    Just "(Quit)" -> putStrLn "Goodbye!"
    Just "(Exit)" -> putStrLn "Goodbye!"
    Just "(Help)" -> do
      putStrLn "Enter a Command, or type `(Quit)` to exit."
      putStrLn ""
      putStrLn "Command ::= (Inhabited Ty)"
      putStrLn "          | (Subtype Ty Ty)"
      putStrLn "          | (Project [1|2] Ty)"
      putStrLn "          | (Apply Ty Ty)"
      putStrLn "          | (Inversion Ty Ty Ty)"
      putStrLn ""
      putStrLn "     Ty ::= Base"
      putStrLn "          | (Arrow Ty Ty)"
      putStrLn "          | (Prod Ty Ty)"
      putStrLn "          | (Or Ty ...)"
      putStrLn "          | (And Ty ...)"
      putStrLn "          | (Not Ty)"
      putStrLn "          | Any"
      putStrLn "          | Empty"
      putStrLn ""
      putStrLn "   Base ::= True | False | String | Integer | Real | Number"
      putStrLn "          | Zero | One | ByteLargerThanOne"
      putStrLn "          | PositiveIndexNotByte | PositiveFixnumNotIndex"
      putStrLn "          | NegativeFixnum | PositiveIntegerNotFixnum"
      putStrLn "          | NegativeIntegerNotFixnum | PositiveRationalNotInteger"
      putStrLn "          | NegativeRationalNotInteger | FloatNaN"
      putStrLn "          | FloatPositiveZero | FloatNegativeZero"
      putStrLn "          | PositiveFloatNumber | PositiveFloatInfinity"
      putStrLn "          | NegativeFloatNumber | NegativeFloatInfinity"
      putStrLn "          | SingleFloatNaN | SingleFloatPositiveZero"
      putStrLn "          | SingleFloatNegativeZero | PositiveSingleFloatNumber"
      putStrLn "          | PositiveSingleFloatInfinity | NegativeSingleFloatNumber"
      putStrLn "          | NegativeSingleFloatInfinity | ExactImaginary"
      putStrLn "          | ExactComplex | FloatImaginary | SingleFloatImaginary"
      putStrLn "          | FloatComplex | SingleFloatComplex | PositiveByte"
      putStrLn "          | Byte | PositiveIndex | Index | PositiveFixnum"
      putStrLn "          | NonnegativeFixnum | NonpositiveFixnum | Fixnum"
      putStrLn "          | PositiveInteger | NonnegativeInteger | NegativeInteger"
      putStrLn "          | NonpositiveInteger | PositiveRational"
      putStrLn "          | NonnegativeRational | NegativeRational"
      putStrLn "          | NonpositiveRational | Rational | FloatZero"
      putStrLn "          | PositiveFloat | NonnegativeFloat | NegativeFloat"
      putStrLn "          | NonpositiveFloat | Float | SingleFloatZero"
      putStrLn "          | InexactRealNaN | InexactRealPositiveZero"
      putStrLn "          | InexactRealNegativeZero | InexactRealZero"
      putStrLn "          | PositiveSingleFloat | PositiveInexactReal"
      putStrLn "          | NonnegativeSingleFloat | NonnegativeInexactReal"
      putStrLn "          | NegativeSingleFloat | NegativeInexactReal"
      putStrLn "          | NonpositiveSingleFloat | NonpositiveInexactReal"
      putStrLn "          | SingleFloat | InexactReal | PositiveInfinity"
      putStrLn "          | NegativeInfinity | RealZero | RealZeroNoNaN"
      putStrLn "          | PositiveReal | NonnegativeReal | NegativeReal"
      putStrLn "          | NonpositiveReal | ExactNumber"
      putStrLn "          | InexactImaginary | Imaginary | InexactComplex"
      runRepl userPrompt
    Just str -> do
      putStrLn (evalString str)
      runRepl userPrompt
    
main :: IO ()
main = do args <- Sys.getArgs
          case args of
               ["test"] -> runComparisonTests
               ["repl"] -> runRepl "> "
               ["pipe"] -> runRepl ""
               otherwise -> putStrLn "usage: numeric-sst [test|repl|pipe]"
  
