module Types.CompareOpTypes where

import Data.List
import Types.LazyBDD
import Types.NumericTower
import Types.Subtype
import Types.Metafunctions
import qualified Types.SyntacticOpTypes as Syn
import qualified Types.SyntacticOpTypesPlus as SynP
import qualified Types.SemanticOpTypes as Sem
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Control.Monad


mTyAnd :: Env -> Ty -> Maybe Ty -> Ty
mTyAnd env t Nothing = t
mTyAnd env t (Just t') = tyAnd env t t'

-- return type using only the first applicable arrow
firstSynUnOpRng :: Env -> [(Ty, Ty)] -> Ty -> Maybe Ty
firstSynUnOpRng env syn arg =
  case (find (\(d,r) -> subtype env arg d) syn) of
    Nothing -> Nothing
    Just (d,r) -> Just r
    

-- return type using _all_ applicable arrows
allSynUnOpRng :: Env -> [(Ty, Ty)] -> Ty -> Maybe Ty
allSynUnOpRng env [] argTy = Nothing
allSynUnOpRng env ((s1,s2):rst) arg
  | (subtype env arg s1) = Just $ mTyAnd env s2 (allSynUnOpRng env rst arg)
  | otherwise = allSynUnOpRng env rst arg

-- return type using _all_ applicable arrows
semUnOpRng :: Env -> [(Ty, Ty)] -> Ty -> Maybe Ty
semUnOpRng env ts arg = rngTy env fun arg
  where fun = parseUnOpToSemantic env ts
          
-- verifies both function types work on the
-- same input types, and that the result for
-- fTy1 is a subtype of the result for fTy2
compareUnOpRes ::
  Env ->
  (Ty -> Maybe Ty)
  -> (Ty -> Maybe Ty)
  -> Ty
  -> Ty
  -> Bool
compareUnOpRes env applyFun1 applyFun2 dom arg =
  case (res1, res2) of
    (Just t1, Just t2) ->
      (subtype env t1 t2) &&
      (((isEmpty env t1) && (isEmpty env t2))
       || (overlap env t1 t2))
    (_,_) -> not $ subtype env arg dom
  where res1 = applyFun1 arg
        res2 = applyFun2 arg

-- identify duplicate cases in case-> if we were
-- to simply apply all possible arrows (returning
-- a list of the indices of the unnecessary arrows)
simplifySynUnOp :: Env -> [(Ty, Ty)] -> [Integer]
simplifySynUnOp env orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2) =
          case (allSynUnOpRng env (delete (t1,t2) orig) t1) of
            Just t -> subtype env t t2
            Nothing -> False

-- like simplifyUnOp
simplifySynBinOp :: Env -> [(Ty, Ty, Ty)] -> [Integer]
simplifySynBinOp env orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                  then Just i
                                  else Nothing)
                   $ zip orig [0..])
        dup (t1,t2,r) =
          case (allSynBinOpRng env (delete (t1,t2,r) orig) t1 t2) of
            Just t -> subtype env t r
            Nothing -> False


firstSynBinOpRng ::
  Env ->
  [(Ty, Ty, Ty)] ->
  Ty ->
  Ty ->
  Maybe Ty
firstSynBinOpRng env syn arg1 arg2 =
  case (find (\(d1,d2,r) ->
                (subtype env arg1 d1)
                && (subtype env arg2 d2)) syn) of
    Nothing -> Nothing
    Just (d1,d2,r) -> Just r


allSynBinOpRng ::
  Env ->
  [(Ty, Ty, Ty)] ->
  Ty ->
  Ty ->
  Maybe Ty
allSynBinOpRng env [] argTy1 argTy2 = Nothing
allSynBinOpRng env ((d1,d2,r):rst) arg1 arg2
  | (subtype env arg1 d1)
    && (subtype env arg2 d2) = Just $ mTyAnd env r (allSynBinOpRng env rst arg1 arg2)
  | otherwise = allSynBinOpRng env rst arg1 arg2


-- return type using _all_ applicable arrows
semBinOpRng :: Env -> [(Ty, Ty, Ty)] -> Ty -> Ty -> Maybe Ty
semBinOpRng env ts arg1 arg2 = (rngTy env fun (prodTy arg1 arg2))
  where fun = parseBinOpToSemantic env ts

compareBinOpRes ::
  Env ->
  (Ty -> Ty -> Maybe Ty)
  -> (Ty -> Ty -> Maybe Ty)
  -> Ty
  -> Ty
  -> Ty
  -> Ty
  -> Bool
compareBinOpRes env applyFun1 applyFun2 dom1 dom2 arg1 arg2 =
    case (res1, res2) of
      (Just t1, Just t2) ->
        (subtype env t1 t2) &&
        (((isEmpty env t1) && (isEmpty env t2)) || (overlap env t1 t2))
      (_,_) -> ((not (subtype env arg1 dom1))
                || (not (subtype env arg2 dom2)))
  where res1 = applyFun1 arg1 arg2
        res2 = applyFun2 arg1 arg2



argType :: Env -> Ty -> Obj -> Prop -> Ty
argType env d  _ FF = emptyTy
argType env d _ TT =  d
argType env d o1 (IsA o2 t)
  | (o1 == o2) = tyAnd env d t
  | otherwise = d
argType env d o1 (Conj p1 p2) = tyAnd env t1 t2
  where t1 = argType env d o1 p1
        t2 = argType env d o1 p2

firstSynCompOpTypes ::
  Env ->
  [(Ty, Ty, Prop, Prop)] ->
  Ty ->
  Ty ->
  Maybe (Ty, Ty, Ty, Ty)
firstSynCompOpTypes env syn arg1 arg2 =
  case (find (\(d1,d2,pos,neg) ->
                (subtype env arg1 d1)
                && (subtype env arg2 d2)) syn) of
    Nothing -> Nothing
    Just (d1,d2, pos, neg) -> Just ((argType env arg1 ArgZero pos),
                                    (argType env arg2 ArgOne pos),
                                    (argType env arg1 ArgZero neg),
                                    (argType env arg2 ArgOne neg))


allSynCompOpTypes ::
  Env ->
  [(Ty, Ty, Prop, Prop)] ->
  Ty ->
  Ty ->
  Maybe (Ty, Ty, Ty, Ty)
allSynCompOpTypes env [] argTy1 argTy2 = Nothing
allSynCompOpTypes env ((d1,d2,pos,neg):rst) arg1 arg2
  | (subtype env arg1 d1)
    && (subtype env arg2 d2) =
    case (allSynCompOpTypes env rst arg1 arg2) of
      Just (pos1, pos2, neg1, neg2) ->
        Just (tyAnd env pos1 (argType env arg1 ArgZero pos),
              tyAnd env pos2 (argType env arg2 ArgOne pos),
              tyAnd env neg1 (argType env arg1 ArgZero neg),
              tyAnd env neg2 (argType env arg2 ArgOne neg)) 
      Nothing -> Just ((argType env arg1 ArgZero pos),
                       (argType env arg2 ArgOne pos),
                       (argType env arg1 ArgZero neg),
                       (argType env arg2 ArgOne neg))
  | otherwise = allSynCompOpTypes env rst arg1 arg2

  
compareCompOpRes ::
  Env ->
  (Ty -> Ty -> Maybe (Ty, Ty, Ty, Ty)) ->
  (Ty -> Ty -> Maybe (Ty, Ty, Ty, Ty)) ->
  Ty ->
  Ty ->
  Ty ->
  Ty ->
  Bool
compareCompOpRes env applyFun1 applyFun2 dom1 dom2 arg1 arg2 =
  case (res1, res2) of
    (Just (pos1,  pos2,  neg1,  neg2),
     Just (pos1', pos2', neg1', neg2')) ->
      if not (subtype env pos1 pos1')
      then error $ "prediction not a subtype for "
           ++ (readBackTy arg1) ++ " " ++ (readBackTy arg2)
           ++ "(pos1): "
           ++ (readBackTy pos1) ++ " </: "
           ++ (readBackTy pos1')
      else if not (subtype env pos2 pos2')
      then error $ "prediction not a subtype for "
           ++ (readBackTy arg1) ++ " " ++ (readBackTy arg2)
           ++ "(pos2): "
           ++ (readBackTy pos2) ++ " </: "
           ++ (readBackTy pos2')
      else if not (subtype env neg1 neg1')
      then error $ "prediction not a subtype for "
           ++ (readBackTy arg1) ++ " " ++ (readBackTy arg2)
           ++ "(neg1): "
           ++ (readBackTy neg1) ++ " </: "
           ++ (readBackTy neg1')
      else if not (subtype env neg2 neg2')
      then error $ "prediction not a subtype for "
           ++ (readBackTy arg1) ++ " " ++ (readBackTy arg2)
           ++ "(neg2): "
           ++ (readBackTy neg2) ++ " </: "
           ++ (readBackTy neg2')
      else True
    (_,_) -> ((not (subtype env arg1 dom1))
              || (not (subtype env arg2 dom2)))
  where res1 = applyFun1 arg1 arg2
        res2 = applyFun2 arg1 arg2



simplifySynCompOp :: Env -> [(Ty, Ty, Prop, Prop)] -> [Integer]
simplifySynCompOp env orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                  then Just i
                                  else Nothing)
                   $ zip orig [0..])
        dup (t1,t2,pos,neg) =
          case (allSynCompOpTypes env (delete (t1,t2,pos,neg) orig) t1 t2) of
            Just (pos1, pos2, neg1, neg2) ->
              (subtype env pos1 (argType env t1 ArgZero pos))
              && (subtype env pos2 (argType env t2 ArgOne pos))
              && (subtype env neg1 (argType env t1 ArgZero neg))
              && (subtype env neg2 (argType env t2 ArgOne neg))
            Nothing -> False


parseUnOpToSemantic :: Env -> [(Ty, Ty)] -> Ty
parseUnOpToSemantic env [] = anyTy
parseUnOpToSemantic env ((d,r):ts) = tyAnd env (arrowTy d r) $ parseUnOpToSemantic env ts


-- identify duplicate cases in case-> if we were
-- to use semantic subtyping-esq function application
simplifySemUnOp :: Env -> [(Ty, Ty)] -> [Integer]
simplifySemUnOp env orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                  then Just i
                                  else Nothing)
                   $ zip orig [0..])
        dup (t1,t2) =
          case (rngTy env
                (parseUnOpToSemantic env (delete (t1,t2) orig))
                t1) of
            Just t -> (subtype env t t2)
            Nothing -> False


parseBinOpToSemantic :: Env -> [(Ty, Ty, Ty)] -> Ty
parseBinOpToSemantic env [] = anyTy
parseBinOpToSemantic env ((d1,d2,r):ts) =
  tyAnd env (arrowTy (prodTy d1 d2) r) $ parseBinOpToSemantic env ts


simplifySemBinOp :: Env -> [(Ty, Ty, Ty)] -> [Integer]
simplifySemBinOp env orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2,r) =
          case (rngTy env
                (parseBinOpToSemantic env (delete (t1,t2,r) orig))
                (prodTy t1 t2)) of
            Just t -> subtype env t r
            Nothing -> False


semCompOpTypes ::
  Env ->
  (Env -> Ty -> Ty -> Ty -> Maybe Ty) ->
  [(Ty, Ty, Ty)] ->
  Ty ->
  Ty ->
  Maybe (Ty, Ty, Ty, Ty)
semCompOpTypes env inputTy ts arg1 arg2 =
  case (pos1,pos2,neg1,neg2) of
    (Just posTy1,
     Just posTy2,
     Just negTy1,
     Just negTy2) -> Just (posTy1, posTy2, negTy1, negTy2)
    (_,_,_,_) -> Nothing
    where argTy = prodTy arg1 arg2
          semTy = parseBinOpToSemantic env ts
          pos = inputTy env semTy argTy $ tyNot env falseTy
          (pos1,pos2) =
            case pos of
              Nothing -> (Nothing, Nothing)
              Just t -> (fstProj env t, sndProj env t)
          neg = inputTy env semTy argTy falseTy
          (neg1,neg2) =
            case neg of
              Nothing -> (Nothing, Nothing)
              Just t -> (fstProj env t, sndProj env t)


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
  Env ->
  [(String, OpSpec)] ->
  (Env -> [(Ty, Ty)] -> Ty -> Maybe Ty) ->
  [(String, OpSpec)] ->
  (Env -> [(Ty, Ty)] -> Ty -> Maybe Ty) ->
  String ->
  IO ()
compareUnOps env ts1 rngTy1 ts2 rngTy2 description = do
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  putStrLn ("Comparing UnOps (" ++ description ++ ")")
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  forM_ unOps $ \(opName, opDom) -> do
    let applyFun1 = (rngTy1 env (getUnOpType opName ts1))
        applyFun2 = (rngTy2 env (getUnOpType opName ts2))
    startTime <- getCurrentTime
    putStr opName
    forM_ numericTypes $ \(argName, argTy) -> do
      putStr (if (compareUnOpRes
                  env
                  applyFun1
                  applyFun2 
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
  Env ->
  [(String, OpSpec)] ->
  ([(Ty, Ty, Ty)] -> Ty -> Ty -> Maybe Ty) ->
  [(String, OpSpec)] ->
  ([(Ty, Ty, Ty)] -> Ty -> Ty -> Maybe Ty) ->
  String ->
  IO ()
compareBinOps env ts1 rngTy1 ts2 rngTy2 description = do
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  putStrLn ("Comparing BinOps (" ++ description ++ ")")
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  forM_ binOps $ \(opName, opDom1, opDom2) -> do
    let applyFun1 = (rngTy1 (getBinOpType opName ts1))
        applyFun2 = (rngTy2 (getBinOpType opName ts2))
    putStr opName
    startTime <- getCurrentTime
    forM_ numericTypes $ \(argName1, argTy1) -> do
      putStr "."
      forM_ numericTypes $ \(argName2, argTy2) -> do
        putStr (if (compareBinOpRes
                    env
                    applyFun1
                    applyFun2
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
  Env ->
  (String -> a) ->
  (a -> Ty -> Ty -> Maybe (Ty, Ty, Ty, Ty)) ->
  (String -> b) ->
  (b -> Ty -> Ty -> Maybe (Ty, Ty, Ty, Ty)) ->
  String ->
  IO ()
compareCompOps env getType1 rngTy1 getType2 rngTy2 description = do
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  putStrLn ("Comparing CompOps (" ++ description ++ ")")
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  forM_ compOps $ \(opName, opDom1, opDom2) -> do
    let applyFun1 = rngTy1 (getType1 opName)
        applyFun2 = rngTy2 (getType2 opName)
    putStr opName
    startTime <- getCurrentTime
    forM_ numericTypes $ \(argName1, argTy1) -> do
      putStr "."
      forM_ numericTypes $ \(argName2, argTy2) -> do
        putStr (if (compareCompOpRes
                    env
                    applyFun1
                    applyFun2
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
   baseEnv
   SynP.opTypes
   allSynUnOpRng
   Syn.opTypes
   firstSynUnOpRng
   descr)

compareSyntacticBinOps :: String -> IO ()
compareSyntacticBinOps descr =
  (compareBinOps
   env
   SynP.opTypes
   (allSynBinOpRng env)
   Syn.opTypes
   (firstSynBinOpRng env)
   "Syntactic/Syntactic+")
  where env = baseEnv


compareSyntacticCompOps :: String -> IO ()
compareSyntacticCompOps descr = 
  (compareCompOps
    env
    (\name -> (getSynCompOpType name SynP.opTypes))
    (allSynCompOpTypes env)
    (\name -> (getSynCompOpType name Syn.opTypes))
    (firstSynCompOpTypes env)
    descr)
  where env = baseEnv

compareSemanticUnOps :: String -> IO ()
compareSemanticUnOps descr =
  (compareUnOps
   env
   Sem.opTypes
   semUnOpRng
   SynP.opTypes
   allSynUnOpRng
   descr)
  where env = baseEnv

compareSemanticBinOps :: String -> IO ()
compareSemanticBinOps descr =
  (compareBinOps
   env
   Sem.opTypes
   (semBinOpRng env)
   SynP.opTypes
   (allSynBinOpRng env)
   descr)
  where env = baseEnv

compareSemanticCompOps :: (Env -> Ty -> Ty -> Ty -> Maybe Ty) -> String -> IO ()
compareSemanticCompOps inputTy descr = 
  (compareCompOps
    env
    (\name -> (getBinOpType name Sem.opTypes))
    (semCompOpTypes env inputTy)
    (\name -> (getSynCompOpType name Syn.opTypes))
    (firstSynCompOpTypes env)
    descr)
  where env = baseEnv
  
