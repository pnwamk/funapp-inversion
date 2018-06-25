module Main where

import Types.Syntax
import qualified Types.SyntacticOpTypes as Syn
import qualified Types.SemanticOpTypes as Sem
import Types.CompareOpTypes

import Data.Foldable


main :: IO ()
main = do
  putStrLn "Comparing inc with base types"
  forM_ baseTypes $ \t -> do
    putStr $ " Comparing in with " ++ (show t) ++ "... "
    putStrLn (if (compareUnOpRes t Sem.incType Syn.incType)
              then ""
              else "failed!")
  putStrLn "Comparing inc with complex types"
  putStrLn "Comparing plus with base types"
  putStrLn "Comparing plus with complex types"
