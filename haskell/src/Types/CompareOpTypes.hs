module Types.CompareOpTypes where

import Data.List
import Types.LazyBDD
import Types.Subtype
import Types.Metafunctions
import Types.BaseEnv
import qualified Types.SyntacticOpTypes as Syn
import qualified Types.SemanticOpTypes as Sem
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Control.Monad

groupOn f = groupBy (\x y -> (f x) == (f y))

mTyAnd :: Ty -> Maybe Ty -> Ty
mTyAnd t Nothing = t
mTyAnd t (Just t') = tyAnd t t'

-- return type using only the first applicable arrow
firstSynUnOpRng :: [(Ty, Ty)] -> Ty -> Maybe Ty
firstSynUnOpRng syn arg =
  case (find (\(d,r) -> subtype arg d) syn) of
    Nothing -> Nothing
    Just (d,r) -> Just r          



firstSynBinOpRng ::
  [(Ty, Ty, Ty)] ->
  Ty ->
  Maybe Ty
firstSynBinOpRng syn arg =
  case (find (\(dom1,dom2,c) -> (subtype arg (prodTy dom1 dom2))) syn) of
    Nothing -> Nothing
    Just (d1,d2,c) -> Just c


-- return type using _all_ applicable arrows
semBinOpRng :: [(Ty, Ty, Ty)] -> Ty ->  Maybe Ty
semBinOpRng ts arg = (rngTy fun arg)
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
  Maybe (Ty, Ty, Ty, Ty)
firstSynCompOpTypes syn arg =
  let (Just arg1) = fstProj arg
      (Just arg2) = sndProj arg in
    case (find (\(d1,d2,pos,neg) -> (subtype arg1 d1) && (subtype arg2 d2)) syn) of
      Nothing -> Nothing
      Just (d1,d2, pos, neg) -> Just ( (argType arg1 ArgZero pos)
                                     , (argType arg2 ArgOne pos)
                                     , (argType arg1 ArgZero neg)
                                     , (argType arg2 ArgOne neg))

  




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
parseBinOpToSemantic ((d1,d2,c):ts) =
  tyAnd (arrowTy (prodTy d1 d2) c) $ parseBinOpToSemantic ts


simplifySemBinOp :: [(Ty, Ty, Ty)] -> [Integer]
simplifySemBinOp orig = [x | Just x <- rawDups]
  where rawDups = (map (\(a,i) -> if dup a
                                 then Just i
                                 else Nothing)
                   $ zip orig [0..])
        dup (d1,d2,c) =
          case (rngTy
                (parseBinOpToSemantic (delete (d1,d2,c) orig))
                (prodTy d1 d2)) of
            Just t -> subtype t c
            Nothing -> False


semCompOpTypes ::
  (Ty -> Ty -> Ty -> Maybe Ty) ->
  [(Ty, Ty, Ty)] ->
  Ty ->
  Maybe (Ty, Ty, Ty, Ty)
semCompOpTypes inputTy ts argTy =
  case (pos1,pos2,neg1,neg2) of
    (Just posTy1,
     Just posTy2,
     Just negTy1,
     Just negTy2) -> Just (posTy1, posTy2, negTy1, negTy2)
    (_,_,_,_) -> Nothing
    where semTy = parseBinOpToSemantic ts
          pos = inputTy semTy argTy $ tyNot falseTy
          (pos1,pos2) =
            case pos of
              Nothing -> (Nothing, Nothing)
              Just t -> (fstProj t, sndProj t)
          neg = inputTy semTy argTy falseTy
          (neg1,neg2) =
            case neg of
              Nothing -> (Nothing, Nothing)
              Just t -> (fstProj t, sndProj t)




-- [(name, domain)]
unOps :: [(String, Ty)]
unOps = [ ("add1", number)
        , ("sub1", number)
        , ("abs", real)
        , ("sqr", number)
        , ("sqrt", number)]
binOps :: [(String, Ty)]
binOps = [("+", number)
         , ("-", number)
         , ("*", number)
         , ("/", number)
         , ("max", real)
         , ("min", real)
         , ("expt", number)
         , ("modulo", integer)
         , ("quotient", integer)]
compOps :: [(String, Ty)]
compOps = [ ("<", real)
          , ("<=", real)
          , ("=", number)]

getUnOpType :: String -> [(String, OpSpec)] -> [(Ty, Ty)]
getUnOpType name table =
  case (lookup name table)  of
    Just (UnOp s) -> s
    Nothing -> error ("missing UnOp spec for " ++ name)


goCompareOps ::
  String ->
  (Ty -> Maybe Ty) ->
  (Ty -> Maybe Ty) ->
  [(String, Ty)] ->
  IO ()
goCompareOps opName f g validArgs = go validArgs 0 0
  where go :: [(String, Ty)] -> Int -> Int -> IO ()
        go [] lts eqs = do
          putStrLn $
            "smaller:    " ++ (show lts)
            ++ "\nequivalent: " ++ (show eqs)
            ++ "\nsmaller/(smaller + equivalent): " ++ (show $ (fromIntegral lts) / (fromIntegral (lts + eqs)))
        go ((argName, t):rst) lts eqs =
          case ((f t), (g t)) of
            (Just res1, Just res2) ->
              case (compareTy res1 res2) of
                LT -> go rst (1 + lts) eqs
                EQ -> go rst lts (1 + eqs)
                GT -> error ("test failed for (" ++ opName ++ " " ++ argName ++ ")")
            (_,_) -> error ("test failed for (" ++ opName ++ " " ++ argName ++ ")")
        
  
compareUnOps ::
  [(String, OpSpec)] ->
  ([(Ty, Ty)] -> Ty -> Maybe Ty) ->
  [(String, OpSpec)] ->
  ([(Ty, Ty)] -> Ty -> Maybe Ty) ->
  String ->
  IO ()
compareUnOps ts1 rngTy1 ts2 rngTy2 description = do
  putStrLn "\n* * * * * * * * * * * * * * * * * * * * * * * * * *"
  putStrLn ("Comparing UnOps (" ++ description ++ ")")
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  forM_ unOps $ \(opName, opDom) -> do
    let applyFun1 = (rngTy1 (getUnOpType opName ts1))
        size1     = length $ (getUnOpType opName ts1)
        applyFun2 = (rngTy2 (getUnOpType opName ts2))
        size2     = length $ (getUnOpType opName ts2)
    putStrLn $ "\n" ++ opName
    putStrLn $ "size change "
      ++ (show size2) ++ " ==> " ++ (show size1) ++ " "
      ++ (show $ (fromIntegral size1) / (fromIntegral size2))
    startTime <- getCurrentTime
    let validArgs = filter (\(_,t) -> subtype t opDom) numericTypes
    goCompareOps opName applyFun1 applyFun2 validArgs
    endTime <- getCurrentTime
    putStrLn $ "(" ++ (show (diffUTCTime endTime startTime)) ++ ")"
    putStrLn "Complete!"


getBinOpType :: String -> [(String, OpSpec)] -> [(Ty, Ty, Ty)]
getBinOpType name table =
  case (lookup name table)  of
    Just (BinOp s) -> s
    Nothing -> error ("missing BinOp spec for " ++ name)
  
compareBinOps ::
  [(String, OpSpec)] ->
  ([(Ty, Ty, Ty)] -> Ty -> Maybe Ty) ->
  [(String, OpSpec)] ->
  ([(Ty, Ty, Ty)] -> Ty -> Maybe Ty) ->
  String ->
  IO ()
compareBinOps ts1 rngTy1 ts2 rngTy2 description = do
  putStrLn "\n* * * * * * * * * * * * * * * * * * * * * * * * * *"
  putStrLn ("Comparing BinOps (" ++ description ++ ")")
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  forM_ binOps $ \(opName, opDom) -> do
    let applyFun1 = rngTy1 $ getBinOpType opName ts1
        size1     = length $ getBinOpType opName ts1
        applyFun2 = rngTy2 $ getBinOpType opName ts2
        size2     = length $ getBinOpType opName ts2
    putStrLn $ "\n" ++ opName
    putStrLn $ "size change "
      ++ (show size2) ++ " ==> " ++ (show size1) ++ " "
      ++ (show $ (fromIntegral size1) / (fromIntegral size2))
    startTime <- getCurrentTime
    let validTys  = filter (\(_,t) -> subtype t opDom) numericTypes
        validArgs = [(n1 ++ " × " ++ n2, (prodTy t1 t2)) | (n1,t1) <- validTys , (n2, t2) <- validTys]
    goCompareOps opName applyFun1 applyFun2 validArgs
    endTime <- getCurrentTime
    putStrLn $ "(" ++ (show (diffUTCTime endTime startTime)) ++ ")"
    putStrLn "Complete!"

getSynCompOpType :: String -> [(String, OpSpec)] -> [(Ty, Ty, Prop, Prop)]
getSynCompOpType name table =
  case (lookup name table)  of
    Just (CompOp s) -> s
    Nothing -> error ("missing CompOp spec for " ++ name)



  
goCompareCompOps ::
  String ->
  (Ty ->  Maybe (Ty, Ty, Ty, Ty)) ->
  (Ty ->  Maybe (Ty, Ty, Ty, Ty)) ->
  [(String, Ty)] ->
  IO ()
goCompareCompOps opName f g validArgs = go validArgs 0 0
  where go :: [(String, Ty)] -> Int -> Int -> IO ()
        go [] lts eqs = do
          putStrLn $
            "smaller predictions:    " ++ (show lts)
            ++ "\nequivalent predictions: " ++ (show eqs)
            ++ "\nsmaller/(smaller + equivalent): " ++ (show $ (fromIntegral lts) / (fromIntegral (lts + eqs)))
        go ((argName, arg):rst) lts eqs =
          case (f arg, g arg) of
            (Just (pos1, pos2, neg1, neg2), Just (pos1', pos2', neg1', neg2')) ->
              case (compareTy pos1 pos1', compareTy pos2 pos2', compareTy neg1 neg1', compareTy neg2 neg2') of
                (GT, _, _, _) -> error $
                                 opName
                                 ++ "prediction not a subtype for "
                                 ++ argName
                                 ++ "(pos1): "
                                 ++ (readBackTy pos1) ++ " </: "
                                 ++ (readBackTy pos1')
                (_, GT, _, _) -> error $
                                 opName
                                 ++ "prediction not a subtype for "
                                 ++ argName 
                                 ++ "(pos2): "
                                 ++ (readBackTy pos2) ++ " </: "
                                 ++ (readBackTy pos2')
                (_, _, GT, _) -> error $
                                 opName
                                 ++ "prediction not a subtype for "
                                 ++ argName 
                                 ++ "(neg1): "
                                 ++ (readBackTy neg1) ++ " </: "
                                 ++ (readBackTy neg1')
                (_, _, _, GT) -> error $
                                 opName
                                 ++ "prediction not a subtype for "
                                 ++ argName 
                                 ++ "(neg2): "
                                 ++ (readBackTy neg2) ++ " </: "
                                 ++ (readBackTy neg2')
                (a, b, c, d)  -> go rst lts' eqs'
                  where lts' = lts + (ltVal a) + (ltVal b) + (ltVal c) + (ltVal d)
                        eqs' = eqs + (eqVal a) + (eqVal b) + (eqVal c) + (eqVal d)
                        ltVal x = if x == LT then 1 else 0
                        eqVal x = if x == EQ then 1 else 0 
            (_,_) -> error ("test failed for (" ++ opName ++ " " ++ argName ++ ")")


compareCompOps ::
  (String -> a) ->
  (a -> Ty -> Maybe (Ty, Ty, Ty, Ty)) ->
  (String -> Int) ->
  (String -> b) ->
  (b -> Ty -> Maybe (Ty, Ty, Ty, Ty)) ->
  (String -> Int) ->
  String ->
  IO ()
compareCompOps getType1 rngTy1 getSize1 getType2 rngTy2 getSize2 description = do
  putStrLn "\n* * * * * * * * * * * * * * * * * * * * * * * * * *"
  putStrLn ("Comparing CompOps (" ++ description ++ ")")
  putStrLn "* * * * * * * * * * * * * * * * * * * * * * * * * *"
  forM_ compOps $ \(opName, opDom) -> do
    let applyFun1 = rngTy1 $ getType1 opName
        size1     = getSize1 opName
        applyFun2 = rngTy2 (getType2 opName)
        size2     = getSize2 opName
    putStrLn $ "\n" ++ opName
    putStrLn $ "size change "
      ++ (show size2) ++ " ==> " ++ (show size1) ++ " "
      ++ (show $ (fromIntegral size1) / (fromIntegral size2))
    startTime <- getCurrentTime
    let validTys  = filter (\(_,t) -> subtype t opDom) numericTypes
        validArgs = [(n1 ++ " × " ++ n2, (prodTy t1 t2)) | (n1,t1) <- validTys , (n2, t2) <- validTys]
    goCompareCompOps opName applyFun1 applyFun2 validArgs
    endTime <- getCurrentTime
    putStrLn $ "(" ++ (show (diffUTCTime endTime startTime)) ++ ")"
    putStrLn "\nComplete!"


-- return type using the semantic approach
semUnOpRng :: [(Ty, Ty)] -> Ty -> Maybe Ty
semUnOpRng ts arg = rngTy fun arg
  where fun = parseUnOpToSemantic ts

compareSemanticUnOps :: String -> IO ()
compareSemanticUnOps descr =
  (compareUnOps
   Sem.opTypes
   semUnOpRng
   Syn.opTypes
   firstSynUnOpRng
   descr)

compareSemanticBinOps :: String -> IO ()
compareSemanticBinOps descr =
  (compareBinOps
   Sem.opTypes
   semBinOpRng
   Syn.opTypes
   firstSynBinOpRng
   descr)

compareSemanticCompOps :: (Ty -> Ty -> Ty -> Maybe Ty) -> String -> IO ()
compareSemanticCompOps inputTy descr = 
  (compareCompOps
    (\name -> getBinOpType name Sem.opTypes)
    (semCompOpTypes inputTy)
    (\name -> length $ getBinOpType name Sem.opTypes)
    (\name -> (getSynCompOpType name Syn.opTypes))
    firstSynCompOpTypes
    (\name -> length $ getSynCompOpType name Syn.opTypes)
    descr)
  
