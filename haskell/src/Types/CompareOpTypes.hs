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


mTyAnd :: Ty -> Maybe Ty -> Ty
mTyAnd t Nothing = t
mTyAnd t (Just t') = tyAnd t t'

-- return type using only the first applicable arrow
firstSynUnOpRng :: [(Ty, Ty)] -> Ty -> Maybe Ty
firstSynUnOpRng syn arg =
  case (find (\(d,r) -> subtype arg d) syn) of
    Nothing -> Nothing
    Just (d,r) -> Just r
    

-- return type using _all_ applicable arrows
allSynUnOpRng :: [(Ty, Ty)] -> Ty -> Maybe Ty
allSynUnOpRng [] argTy = Nothing
allSynUnOpRng ((s1,s2):rst) arg
  | (subtype arg s1) = Just $ mTyAnd s2 (allSynUnOpRng rst arg)
  | otherwise = allSynUnOpRng rst arg

-- return type using _all_ applicable arrows
semUnOpRng :: [(Ty, Ty)] -> Ty -> Maybe Ty
semUnOpRng ts arg = rngTy fun arg
  where fun = parseUnOpToSemantic ts
          
-- verifies both function types work on the
-- same input types, and that the result for
-- fTy1 is a subtype of the result for fTy2
compareUnOpRes ::
  (Ty -> Maybe Ty)
  -> (Ty -> Maybe Ty)
  -> Ty
  -> Ty
  -> Bool
compareUnOpRes applyFun1 applyFun2 dom arg =
  case (res1, res2) of
    (Just t1, Just t2) -> (subtype t1 t2) &&
                          (((isEmpty t1) && (isEmpty t2)) || (overlap t1 t2))
    (_,_) -> not $ subtype arg dom
  where res1 = applyFun1 arg
        res2 = applyFun2 arg

-- identify duplicate cases in case-> if we were
-- to simply apply all possible arrows (returning
-- a list of the indices of the unnecessary arrows)
simplifySynUnOp :: [(Ty, Ty)] -> [Integer]
simplifySynUnOp orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2) =
          case (allSynUnOpRng (delete (t1,t2) orig) t1) of
            Just t -> subtype t t2
            Nothing -> False

-- like simplifyUnOp
simplifySynBinOp :: [(Ty, Ty, Ty)] -> [Integer]
simplifySynBinOp orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2,r) =
          case (allSynBinOpRng (delete (t1,t2,r) orig) t1 t2) of
            Just t -> subtype t r
            Nothing -> False


firstSynBinOpRng ::
  [(Ty, Ty, Ty)] ->
  Ty ->
  Ty ->
  Maybe Ty
firstSynBinOpRng syn arg1 arg2 =
  case (find (\(d1,d2,r) -> (subtype arg1 d1) && (subtype arg2 d2)) syn) of
    Nothing -> Nothing
    Just (d1,d2,r) -> Just r


allSynBinOpRng ::
  [(Ty, Ty, Ty)] ->
  Ty ->
  Ty ->
  Maybe Ty
allSynBinOpRng [] argTy1 argTy2 = Nothing
allSynBinOpRng ((d1,d2,r):rst) arg1 arg2
  | (subtype arg1 d1)
    && (subtype arg2 d2) = Just $ mTyAnd r (allSynBinOpRng rst arg1 arg2)
  | otherwise = allSynBinOpRng rst arg1 arg2


-- return type using _all_ applicable arrows
semBinOpRng :: [(Ty, Ty, Ty)] -> Ty -> Ty -> Maybe Ty
semBinOpRng ts arg1 arg2 = (rngTy fun (prodTy arg1 arg2))
  where fun = parseBinOpToSemantic ts

compareBinOpRes ::
  (Ty -> Ty -> Maybe Ty)
  -> (Ty -> Ty -> Maybe Ty)
  -> Ty
  -> Ty
  -> Ty
  -> Ty
  -> Bool
compareBinOpRes applyFun1 applyFun2 dom1 dom2 arg1 arg2 =
    case (res1, res2) of
      (Just t1, Just t2) -> (subtype t1 t2) &&
                            (((isEmpty t1) && (isEmpty t2)) || (overlap t1 t2))
      (_,_) -> ((not (subtype arg1 dom1))
                || (not (subtype arg2 dom2)))
  where res1 = applyFun1 arg1 arg2
        res2 = applyFun2 arg1 arg2



argType :: Ty -> Obj -> Prop -> Ty
argType d  _ FF = emptyTy
argType d _ TT =  d
argType d o1 (IsA o2 t)
  | (o1 == o2) = tyAnd d t
  | otherwise = d
argType d o1 (Conj p1 p2) = tyAnd t1 t2
  where t1 = argType d o1 p1
        t2 = argType d o1 p2

firstSynCompOpTypes ::
  [(Ty, Ty, Prop, Prop)] ->
  Ty ->
  Ty ->
  Maybe (Ty, Ty, Ty, Ty)
firstSynCompOpTypes syn arg1 arg2 =
  case (find (\(d1,d2,pos,neg) -> (subtype arg1 d1) && (subtype arg2 d2)) syn) of
    Nothing -> Nothing
    Just (d1,d2, pos, neg) -> Just ((argType arg1 ArgZero pos),
                                    (argType arg2 ArgOne pos),
                                    (argType arg1 ArgZero neg),
                                    (argType arg2 ArgOne neg))


allSynCompOpTypes ::
  [(Ty, Ty, Prop, Prop)] ->
  Ty ->
  Ty ->
  Maybe (Ty, Ty, Ty, Ty)
allSynCompOpTypes [] argTy1 argTy2 = Nothing
allSynCompOpTypes ((d1,d2,pos,neg):rst) arg1 arg2
  | (subtype arg1 d1)
    && (subtype arg2 d2) =
    case (allSynCompOpTypes rst arg1 arg2) of
      Just (pos1, pos2, neg1, neg2) ->
        Just (tyAnd pos1 (argType arg1 ArgZero pos),
              tyAnd pos2 (argType arg2 ArgOne pos),
              tyAnd neg1 (argType arg1 ArgZero neg),
              tyAnd neg2 (argType arg2 ArgOne neg)) 
      Nothing -> Just ((argType arg1 ArgZero pos),
                       (argType arg2 ArgOne pos),
                       (argType arg1 ArgZero neg),
                       (argType arg2 ArgOne neg))
  | otherwise = allSynCompOpTypes rst arg1 arg2

  
compareCompOpRes ::
  (Ty -> Ty -> Maybe (Ty, Ty, Ty, Ty)) ->
  (Ty -> Ty -> Maybe (Ty, Ty, Ty, Ty)) ->
  Ty ->
  Ty ->
  Ty ->
  Ty ->
  Bool
compareCompOpRes applyFun1 applyFun2 dom1 dom2 arg1 arg2 =
  case (res1, res2) of
    (Just (pos1, pos2, neg1, neg2), Just (pos1', pos2', neg1', neg2')) ->
      (subtype pos1 pos1')
      && (subtype pos2 pos2')
      && (subtype neg1 neg1')
      && (subtype neg2 neg2')
    (_,_) -> ((not (subtype arg1 dom1))
              || (not (subtype arg2 dom2)))
  where res1 = applyFun1 arg1 arg2
        res2 = applyFun2 arg1 arg2



simplifySynCompOp :: [(Ty, Ty, Prop, Prop)] -> [Integer]
simplifySynCompOp orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2,pos,neg) =
          case (allSynCompOpTypes (delete (t1,t2,pos,neg) orig) t1 t2) of
            Just (pos1, pos2, neg1, neg2) ->
              (subtype pos1 (argType t1 ArgZero pos))
              && (subtype pos2 (argType t2 ArgOne pos))
              && (subtype neg1 (argType t1 ArgZero neg))
              && (subtype neg2 (argType t2 ArgOne neg))
            Nothing -> False


parseUnOpToSemantic :: [(Ty, Ty)] -> Ty
parseUnOpToSemantic [] = anyTy
parseUnOpToSemantic ((d,r):ts) = tyAnd (arrowTy d r) $ parseUnOpToSemantic ts


-- identify duplicate cases in case-> if we were
-- to use semantic subtyping-esq function application
simplifySemUnOp :: [(Ty, Ty)] -> [Integer]
simplifySemUnOp orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2) =
          case (rngTy
                (parseUnOpToSemantic (delete (t1,t2) orig))
                t1) of
            Just t -> (subtype t t2)
            Nothing -> False


parseBinOpToSemantic :: [(Ty, Ty, Ty)] -> Ty
parseBinOpToSemantic [] = anyTy
parseBinOpToSemantic ((d1,d2,r):ts) =
  tyAnd (arrowTy (prodTy d1 d2) r) $ parseBinOpToSemantic ts


simplifySemBinOp :: [(Ty, Ty, Ty)] -> [Integer]
simplifySemBinOp orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (t1,t2,r) =
          case (rngTy
                (parseBinOpToSemantic (delete (t1,t2,r) orig))
                (prodTy t1 t2)) of
            Just t -> subtype t r
            Nothing -> False


semCompOpTypes ::
  (Ty -> Ty -> Ty -> Maybe Ty) ->
  [(Ty, Ty, Ty)] ->
  Ty ->
  Ty ->
  Maybe (Ty, Ty, Ty, Ty)
semCompOpTypes inputTy ts arg1 arg2 =
  case (pos1,pos2,neg1,neg2) of
    (Just posTy1,
     Just posTy2,
     Just negTy1,
     Just negTy2) -> Just (posTy1, posTy2, negTy1, negTy2)
    (_,_,_,_) -> Nothing
    where argTy = prodTy arg1 arg2
          semTy = parseBinOpToSemantic ts
          pos = inputTy semTy argTy $ tyNot false
          (pos1,pos2) =
            case pos of
              Nothing -> (Nothing, Nothing)
              Just t -> (fstProj t, sndProj t)
          neg = inputTy semTy argTy false
          (neg1,neg2) =
            case neg of
              Nothing -> (Nothing, Nothing)
              Just t -> (fstProj t, sndProj t)




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
  ([(Ty, Ty)] -> Ty -> Maybe Ty) ->
  [(String, OpSpec)] ->
  ([(Ty, Ty)] -> Ty -> Maybe Ty) ->
  String ->
  IO ()
compareUnOps ts1 rngTy1 ts2 rngTy2 description = do
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  putStrLn ("Comparing UnOps (" ++ description ++ ")")
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  forM_ unOps $ \(opName, opDom) -> do
    let applyFun1 = (rngTy1 (getUnOpType opName ts1))
        applyFun2 = (rngTy2 (getUnOpType opName ts2))
    startTime <- getCurrentTime
    putStr opName
    forM_ numericTypes $ \(argName, argTy) -> do
      putStr (if (compareUnOpRes
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
  [(String, OpSpec)] ->
  ([(Ty, Ty, Ty)] -> Ty -> Ty -> Maybe Ty) ->
  [(String, OpSpec)] ->
  ([(Ty, Ty, Ty)] -> Ty -> Ty -> Maybe Ty) ->
  String ->
  IO ()
compareBinOps ts1 rngTy1 ts2 rngTy2 description = do
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
  (String -> a) ->
  (a -> Ty -> Ty -> Maybe (Ty, Ty, Ty, Ty)) ->
  (String -> b) ->
  (b -> Ty -> Ty -> Maybe (Ty, Ty, Ty, Ty)) ->
  String ->
  IO ()
compareCompOps getType1 rngTy1 getType2 rngTy2 description = do
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

compareSemanticCompOps :: (Ty -> Ty -> Ty -> Maybe Ty) -> String -> IO ()
compareSemanticCompOps inputTy descr = 
  (compareCompOps
    (\name -> (getBinOpType name Sem.opTypes))
    (semCompOpTypes inputTy)
    (\name -> (getSynCompOpType name Syn.opTypes))
    firstSynCompOpTypes
    descr)
  
