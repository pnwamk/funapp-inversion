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
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Data.Foldable
import Control.Monad
import Types.Parse


-- [(name, domain)]
unOps :: [(String, Ty)]
unOps = [ ("add1", number)
        , ("sub1", number)
        , ("abs", real)]

binOps :: [(String, Ty, Ty)]
binOps = [("+", number, number)
         , ("-", number, number)
         , ("*", number, number)
         , ("/", number, number)
         , ("max", real, real)
         , ("min", real, real)]

compOps :: [(String, Ty, Ty)]
compOps = [ ("<", real, real)
          , ("<=", real, real)
          , ("=", number, number)]

getUnOpType :: String -> [(String, OpSpec)] -> [(Ty, Ty)]
getUnOpType name table =
  case (lookup name table)  of
    Just (UnOp s) -> s
    Nothing -> error ("missing UnOp spec for " ++ name)
  
compareUnOps ::
  [(String, OpSpec)] ->
  ([(Ty, Ty)] -> Ty -> Maybe BDD.Ty) ->
  [(String, OpSpec)] ->
  ([(Ty, Ty)] -> Ty -> Maybe BDD.Ty) ->
  String ->
  IO ()
compareUnOps ts1 rngTy1 ts2 rngTy2 description = do
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  putStrLn ("Comparing UnOps (" ++ description ++ ")")
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  forM_ unOps $ \(opName, opDom) -> do
    startTime <- getCurrentTime
    putStr opName
    forM_ numericTypes $ \(argName, argTy) -> do
      putStr (if (compareUnOpRes
                  (getUnOpType opName ts1)
                  rngTy1
                  (getUnOpType opName ts2)
                  rngTy2
                  opDom
                  argTy)
              then "."
              else error ("test failed for ("
                          ++ opName ++ " " ++ argName ++ ")"))
    endTime <- getCurrentTime
    putStrLn $ "(" ++ (show (diffUTCTime endTime startTime)) ++ ")"

  putStrLn "\nComplete!"


getBinOpType :: String -> [(String, OpSpec)] -> [(Ty, Ty, Ty)]
getBinOpType name table =
  case (lookup name table)  of
    Just (BinOp s) -> s
    Nothing -> error ("missing BinOp spec for " ++ name)
  
compareBinOps ::
  [(String, OpSpec)] ->
  ([(Ty, Ty, Ty)] -> Ty -> Ty -> Maybe BDD.Ty) ->
  [(String, OpSpec)] ->
  ([(Ty, Ty, Ty)] -> Ty -> Ty -> Maybe BDD.Ty) ->
  String ->
  IO ()
compareBinOps ts1 rngTy1 ts2 rngTy2 description = do
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  putStrLn ("Comparing BinOps (" ++ description ++ ")")
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  forM_ binOps $ \(opName, opDom1, opDom2) -> do
    startTime <- getCurrentTime
    putStr opName
    forM_ numericTypes $ \(argName1, argTy1) -> do
      putStr "."
      forM_ numericTypes $ \(argName2, argTy2) -> do
        putStr (if (compareBinOpRes
                    (getBinOpType opName ts1)
                    rngTy1
                    (getBinOpType opName ts2)
                    rngTy2
                    opDom1
                    opDom2
                    argTy1
                    argTy2)
                then ""
                else error ("test failed for ("
                            ++ opName ++ " "
                            ++ argName1 ++ " "
                            ++ argName2 ++ ")"))
    endTime <- getCurrentTime
    putStrLn $ "(" ++ (show (diffUTCTime endTime startTime)) ++ ")"

  putStrLn "\nComplete!"

getSynCompOpType :: String -> [(String, OpSpec)] -> [(Ty, Ty, Prop, Prop)]
getSynCompOpType name table =
  case (lookup name table)  of
    Just (CompOp s) -> s
    Nothing -> error ("missing CompOp spec for " ++ name)

compareCompOps ::
  (String -> a) ->
  (a -> Ty -> Ty -> Maybe (BDD.Ty, BDD.Ty, BDD.Ty, BDD.Ty)) ->
  (String -> b) ->
  (b -> Ty -> Ty -> Maybe (BDD.Ty, BDD.Ty, BDD.Ty, BDD.Ty)) ->
  String ->
  IO ()
compareCompOps getType1 rngTy1 getType2 rngTy2 description = do
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  putStrLn ("Comparing CompOps (" ++ description ++ ")")
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  forM_ compOps $ \(opName, opDom1, opDom2) -> do
    startTime <- getCurrentTime
    putStr opName
    forM_ numericTypes $ \(argName1, argTy1) -> do
      putStr "."
      forM_ numericTypes $ \(argName2, argTy2) -> do
        putStr (if (compareCompOpRes
                    (getType1 opName)
                    rngTy1
                    (getType2 opName)
                    rngTy2
                    opDom1
                    opDom2
                    argTy1
                    argTy2)
                then ""
                else error ("test failed for ("
                            ++ opName ++ " "
                            ++ argName1 ++ " "
                            ++ argName2 ++ ")"))
    endTime <- getCurrentTime
    putStrLn $ "(" ++ (show (diffUTCTime endTime startTime)) ++ ")"

  putStrLn "\nComplete!"

compareSyntacticUnOps :: String -> IO ()
compareSyntacticUnOps descr =
  (compareUnOps
   SynP.opTypes
   allSynUnOpRng
   Syn.opTypes
   firstSynUnOpRng
   descr)

compareSyntacticBinOps :: String -> IO ()
compareSyntacticBinOps descr =
  (compareBinOps
   SynP.opTypes
   allSynBinOpRng
   Syn.opTypes
   firstSynBinOpRng
   "Syntactic/Syntactic+")

compareSyntacticCompOps :: String -> IO ()
compareSyntacticCompOps descr = 
  (compareCompOps
    (\name -> (getSynCompOpType name SynP.opTypes))
    allSynCompOpTypes
    (\name -> (getSynCompOpType name Syn.opTypes))
    firstSynCompOpTypes
    descr)

compareSemanticUnOps :: String -> IO ()
compareSemanticUnOps descr =
  (compareUnOps
   Sem.opTypes
   semUnOpRng
   SynP.opTypes
   allSynUnOpRng
   descr)

compareSemanticBinOps :: String -> IO ()
compareSemanticBinOps descr =
  (compareBinOps
   Sem.opTypes
   semBinOpRng
   SynP.opTypes
   allSynBinOpRng
   descr)

compareSemanticCompOps :: (BDD.Ty -> BDD.Ty -> BDD.Ty -> Maybe BDD.Ty) -> String -> IO ()
compareSemanticCompOps inputTy descr = 
  (compareCompOps
    (\name -> (getBinOpType name Sem.opTypes))
    (semCompOpTypes inputTy)
    (\name -> (getSynCompOpType name Syn.opTypes))
    firstSynCompOpTypes
    descr)

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

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

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

evalAndPrint :: String -> IO ()
evalAndPrint expr =  putStrLn (evalString expr)

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ pred prompt action = do 
   result <- prompt
   if pred result 
      then return ()
      else action result >> until_ pred prompt action

runRepl :: IO ()
runRepl = do
  until_ (== "quit") (readPrompt "> ") evalAndPrint
  
main :: IO ()
main = do args <- Sys.getArgs
          case args of
               ["test"] -> runComparisonTests
               ["repl"] -> runRepl
               otherwise -> putStrLn "usage: numeric-sst [test|repl]"
  
