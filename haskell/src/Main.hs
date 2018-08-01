module Main where

import Types.Syntax
import qualified Types.LazyBDD as BDD
import Types.Subtype
import Types.Metafunctions
import qualified Types.SyntacticOpTypes as Syn
import qualified Types.SyntacticOpTypesPlus as SynP
import Types.CompareOpTypes
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Data.Foldable
import Control.Monad

-- timeInc :: IO ()
-- timeInc = do
--   putStrLn "* * * * * * * * * * * * * * * * * * * *"
--   putStrLn "Comparing inc: "
--   incStart <- getCurrentTime
--   forM_ numericTypes $ \(name, ty) -> do
--     putStr $ "  " ++ name ++ " ... "
--     start <- getCurrentTime
--     result <- pure $! compareUnOpRes number ty Sem.incType Syn.incType
--     end <- getCurrentTime
--     putStr $ "(" ++ (show (diffUTCTime end start)) ++ ")"
--     putStrLn (if result
--               then ""
--               else error "failed!")
--   incEnd <- getCurrentTime
--   putStrLn $ "inc total time: " ++ (show (diffUTCTime incEnd incStart))
--   putStrLn "* * * * * * * * * * * * * * * * * * * *"


-- timePlus :: IO ()
-- timePlus = do
--   putStrLn "* * * * * * * * * * * * * * * * * * * *"
--   putStrLn "Comparing plus:"
--   plusStart <- getCurrentTime
--   forM_ numericTypes $ \(name1, ty1) -> do
--     forM_ numericTypes $ \(name2, ty2) -> do
--       putStr $ "  " ++ name1 ++ " x " ++ name2 ++ " ... "
--       start <- getCurrentTime
--       result <- pure $! compareBinOpRes number number ty1 ty2 Sem.plusType Syn.plusType
--       end <- getCurrentTime
--       putStr $ "(" ++ (show (diffUTCTime end start)) ++ ")"
--       putStrLn (if result
--                 then ""
--                 else error "failed!")
--   plusEnd <- getCurrentTime
--   putStrLn $ "plus total time: " ++ (show (diffUTCTime plusEnd plusStart))
--   putStrLn "* * * * * * * * * * * * * * * * * * * *"


-- timeLT :: (BDD.Ty -> BDD.Ty -> BDD.Ty -> Maybe BDD.Ty) -> IO ()
-- timeLT inputTy = do
--   putStrLn "* * * * * * * * * * * * * * * * * * * *"
--   putStrLn "Comparing less-than:"
--   ltStart <- getCurrentTime
--   forM_ numericTypes $ \(name1, ty1) -> do
--     forM_ numericTypes $ \(name2, ty2) -> do
--       when ((subtype (BDD.parseTy ty1) (BDD.parseTy real))
--             && (subtype (BDD.parseTy ty2) (BDD.parseTy real))) $ do
--         putStr $ "  " ++ name1 ++ " x " ++ name2 ++ " ... "
--         start <- getCurrentTime
--         result <- pure $! compareBinPredRes inputTy real real ty1 ty2 Sem.ltType Syn.ltType
--         end <- getCurrentTime
--         putStr $ "(" ++ (show (diffUTCTime end start)) ++ ")"
--         putStrLn (if result
--                   then ""
--                   else error "failed!")
--   ltEnd <- getCurrentTime
--   putStrLn $ "less-than total time: " ++ (show (diffUTCTime ltEnd ltStart))
--   putStrLn "* * * * * * * * * * * * * * * * * * * *"

-- [(name, domain)]
unOps :: [(String, Ty)]
unOps = [ ("add1", number)
        , ("sub1", number)
        , ("abs", real)]

binOps :: [(String, Ty, Ty)]
binOps = [ ("+", number, number)
         , ("-", number, number)
         , ("*", number, number)
         , ("/", number, number)
         , ("max", real, real)
         , ("min", real, real)]

compOps :: [(String, Ty, Ty)]
compOps = [ ("<", real, real)
          , ("<=", real, real)]

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
  putStr ("Comparing UnOps (" ++ description ++ ")")
  forM_ unOps $ \(opName, opDom) -> do
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
  putStrLn "Complete!"


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
  putStr ("Comparing BinOps (" ++ description ++ ")")
  forM_ binOps $ \(opName, opDom1, opDom2) -> do
    forM_ numericTypes $ \(argName1, argTy1) -> do
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
                then "."
                else error ("test failed for ("
                            ++ opName ++ " "
                            ++ argName1 ++ " "
                            ++ argName2 ++ ")"))
  putStrLn "Complete!"

getCompOpType :: String -> [(String, OpSpec)] -> [(Ty, Ty, Prop, Prop)]
getCompOpType name table =
  case (lookup name table)  of
    Just (CompOp s) -> s
    Nothing -> error ("missing CompOp spec for " ++ name)

compareCompOps ::
  [(String, OpSpec)] ->
  ([(Ty, Ty, Prop, Prop)] -> Ty -> Ty -> Maybe (Prop, Prop)) ->
  [(String, OpSpec)] ->
  ([(Ty, Ty, Prop, Prop)] -> Ty -> Ty -> Maybe (Prop, Prop)) ->
  String ->
  IO ()
compareCompOps ts1 rngTy1 ts2 rngTy2 description = do
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  putStr ("Comparing CompOps (" ++ description ++ ")")
  forM_ compOps $ \(opName, opDom1, opDom2) -> do
    forM_ numericTypes $ \(argName1, argTy1) -> do
      forM_ numericTypes $ \(argName2, argTy2) -> do
        putStr (if (compareCompOpRes
                    (getCompOpType opName ts1)
                    rngTy1
                    (getCompOpType opName ts2)
                    rngTy2
                    opDom1
                    opDom2
                    argTy1
                    argTy2)
                then "."
                else error ("test failed for ("
                            ++ opName ++ " "
                            ++ argName1 ++ " "
                            ++ argName2 ++ ")"))
  putStrLn "Complete!"

main :: IO ()
main = do
  -- (compareUnOps
  --  SynP.opTypes
  --  allSynUnOpRng
  --  Syn.opTypes
  --  firstSynUnOpRng
  --  "Syntactic/Syntactic+")
  -- (compareBinOps
  --  SynP.opTypes
  --  allSynBinOpRng
  --  Syn.opTypes
  --  firstSynBinOpRng
  --  "Syntactic/Syntactic+")
  (compareCompOps
   SynP.opTypes
   allSynCompOpProps
   Syn.opTypes
   firstSynCompOpProps
   "Syntactic/Syntactic+")
  --timeInc
  --timePlus
  -- timeLT inTy
  -- timeLT cInTy

  
