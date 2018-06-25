module Main where

import Types.Syntax
import qualified Types.SyntacticOpTypes as Syn
import qualified Types.SemanticOpTypes as Sem
import Types.CompareOpTypes

import Data.Foldable


main :: IO ()
main = do
  putStrLn "Comparing inc: "
  forM_ numericTypes $ \(name, ty) -> do
    putStr $ "  " ++ name ++ " ... "
    putStrLn (if (compareUnOpRes ty Sem.incType Syn.incType)
              then ""
              else "failed!")
  putStrLn "Comparing plus:"
  forM_ numericTypes $ \(name1, ty1) -> do
    forM_ numericTypes $ \(name2, ty2) -> do
      putStr $ "  " ++ name1 ++ " x " ++ name2 ++ " ... "
      putStrLn (if (compareBinOpRes ty1 ty2 Sem.plusType Syn.plusType)
              then ""
              else "failed!")
  
