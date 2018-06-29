module Main where

import Types.Syntax
import qualified Types.LazyBDD as BDD
import Types.Subtype
import Types.Metafunctions
import qualified Types.SyntacticOpTypes as Syn
import qualified Types.SemanticOpTypes as Sem
import Types.CompareOpTypes
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Data.Foldable
import Control.Monad

timeInc :: IO ()
timeInc = do
  putStrLn "* * * * * * * * * * * * * * * * * * * *"
  putStrLn "Comparing inc: "
  incStart <- getCurrentTime
  forM_ numericTypes $ \(name, ty) -> do
    putStr $ "  " ++ name ++ " ... "
    start <- getCurrentTime
    result <- pure $! compareUnOpRes number ty Sem.incType Syn.incType
    end <- getCurrentTime
    putStr $ "(" ++ (show (diffUTCTime end start)) ++ ")"
    putStrLn (if result
              then ""
              else error "failed!")
  incEnd <- getCurrentTime
  putStrLn $ "inc total time: " ++ (show (diffUTCTime incEnd incStart))
  putStrLn "* * * * * * * * * * * * * * * * * * * *"


timePlus :: IO ()
timePlus = do
  putStrLn "* * * * * * * * * * * * * * * * * * * *"
  putStrLn "Comparing plus:"
  plusStart <- getCurrentTime
  forM_ numericTypes $ \(name1, ty1) -> do
    forM_ numericTypes $ \(name2, ty2) -> do
      putStr $ "  " ++ name1 ++ " x " ++ name2 ++ " ... "
      start <- getCurrentTime
      result <- pure $! compareBinOpRes number number ty1 ty2 Sem.plusType Syn.plusType
      end <- getCurrentTime
      putStr $ "(" ++ (show (diffUTCTime end start)) ++ ")"
      putStrLn (if result
                then ""
                else error "failed!")
  plusEnd <- getCurrentTime
  putStrLn $ "plus total time: " ++ (show (diffUTCTime plusEnd plusStart))
  putStrLn "* * * * * * * * * * * * * * * * * * * *"


timeLT :: (BDD.Ty -> BDD.Ty -> BDD.Ty -> Maybe BDD.Ty) -> IO ()
timeLT inputTy = do
  putStrLn "* * * * * * * * * * * * * * * * * * * *"
  putStrLn "Comparing less-than:"
  ltStart <- getCurrentTime
  forM_ numericTypes $ \(name1, ty1) -> do
    forM_ numericTypes $ \(name2, ty2) -> do
      when ((subtype (BDD.parseTy ty1) (BDD.parseTy real))
            && (subtype (BDD.parseTy ty2) (BDD.parseTy real))) $ do
        putStr $ "  " ++ name1 ++ " x " ++ name2 ++ " ... "
        start <- getCurrentTime
        result <- pure $! compareBinPredRes inputTy real real ty1 ty2 Sem.ltType Syn.ltType
        end <- getCurrentTime
        putStr $ "(" ++ (show (diffUTCTime end start)) ++ ")"
        putStrLn (if result
                  then ""
                  else error "failed!")
  ltEnd <- getCurrentTime
  putStrLn $ "less-than total time: " ++ (show (diffUTCTime ltEnd ltStart))
  putStrLn "* * * * * * * * * * * * * * * * * * * *"



main :: IO ()
main = do
  --timeInc
  --timePlus
  timeLT inTy
  timeLT cInTy

  
