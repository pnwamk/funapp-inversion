module Types.SubtypeTests (genSubtypeSpec) where


import Test.Hspec
import Test.QuickCheck
import Types.Syntax


genSubtypeSpec ::
  (Ty -> a)
  -> (a -> a -> Bool)
  -> (a -> a -> Bool)
  -> (a -> a -> Bool)
  -> Spec
genSubtypeSpec parse rawSubtype rawOverlap rawEquiv = do
  describe "Basic Subtyping Properties" $ do
    it "Simple Explicit Tests" $ do
      (runSubtypeTests subtype) `shouldBe` ["All tests passed!"]
    it "Reflexivity" $ property $
      \t -> subtype t t
    it "Base/Prod disjoint" $ property $
      \t1 t2 -> not (overlap (Base T) (Prod t1 t2))
    it "Base/Arrow disjoint" $ property $
      \t1 t2 -> not (overlap (Base T) (Arrow t1 t2))
    it "Prod/Arrow disjoint" $ property $
      \t1 t2 t3 t4 -> not (overlap (Arrow t1 t2) (Prod t3 t4))
    it "OrR1" $ property $
      \t1 t2 -> subtype t1 (Or [t1, t2])
    it "OrR2" $ property $
      \t1 t2 -> subtype t2 (Or [t1, t2])
    it "AndL1" $ property $
      \t1 t2 -> subtype (And [t1, t2]) t1
    it "AndL2" $ property $
      \t1 t2 -> subtype (And [t1, t2]) t2
    it "NotOr" $ property $
      \t1 t2 -> subtype (Not (Or [t1, t2])) (Not t1)
    it "ProdL" $ property $
      \t1 t2 -> if subtype t1 t2
                then subtype (Prod t1 Any) (Prod t2 Any)
                else not (subtype (Prod t1 Any) (Prod t2 Any))
    it "ProdR" $ property $
      \t1 t2 -> if subtype t1 t2
                then subtype (Prod Any t1) (Prod Any t2)
                else not (subtype (Prod Any t1) (Prod Any t2))
    it "ProdNotL" $ property $
      \t1 t2 t3 -> (subtype
                    (And [(Prod (Or [t1,t2]) t3),
                          (Prod (Not t1) t3)])
                    (Prod t2 t3))
    it "ProdNotR" $ property $
      \t1 t2 t3 -> (subtype
                    (And [(Prod t1 (Or [t2,t3])),
                          (Prod t1 (Not t2))])
                    (Prod t1 t3))
    it "ProdOr" $ property $
      \t1 t2 t3 t4 t5 t6 ->
        (subtype
          (Or [(Prod t1 t2),
               (Prod t3 t4),
               (Prod t5 t6)])
          (Prod (Or [t1,t3,t5]) (Or [t2,t4,t6])))
    it "ProdAnd" $ property $
      \t1 t2 t3 t4 t5 t6 ->
        (equiv
          (And [(Prod t1 t2),
                (Prod t3 t4),
                (Prod t5 t6)])
          (Prod (And [t1,t3,t5]) (And [t2,t4,t6])))
    it "ArrowContraCo" $ property $
      \t1 t2 t3 t4 t5 t6 ->
        (subtype
          (Arrow (Or [t1,t3,t5]) t2)
          (Arrow t1 (Or [t2,t4,t6])))
    it "ArrowAnd" $ property $
      \t1 t2 t3 t4 t5 t6 ->
        (subtype
          (And [(Arrow t1 t2),
                (Arrow t3 t4),
                (Arrow t5 t6)])
          (Arrow t1 t2))
    it "ArrowAndOr" $ property $
      \t1 t2 t3 t4 t5 t6 ->
        (subtype
          (And [(Arrow t1 t2),
                (Arrow t3 t4),
                (Arrow t5 t6)])
          (Arrow (Or [t1,t3,t5]) (Or [t2,t4,t6])))
    it "ArrowAndAnd" $ property $
      \t1 t2 t3 t4 t5 t6 ->
        (subtype
          (And [(Arrow t1 t2),
                (Arrow (Or [t1,t3]) t4),
                (Arrow t5 t6)])
          (Arrow t1 (And [t2,t4])))


  describe "Logical Equivalences" $ do
    it "And Commutativity" $ property $
      \t1 t2 -> equiv (And [t1, t2]) (And [t2, t1])
    it "And Associativity" $ property $
      \t1 t2 t3 -> equiv (And [t1, (And [t2, t3])]) (And [(And [t1, t2]), t3])
    it "Or Commutativity" $ property $
      \t1 t2 -> equiv (Or [t1, t2]) (Or [t2, t1])
    it "Or Associativity" $ property $
      \t1 t2 t3 -> equiv (Or [t1, (Or [t2, t3])]) (Or [(Or [t1, t2]), t3])
    it "Or Distribution" $ property $
      \t1 t2 t3 -> equiv (Or [t1, (And [t2, t3])]) (And [(Or [t1, t2]), (Or [t1, t3])])
    it "And Distribution" $ property $
      \t1 t2 t3 -> equiv (And [t1, (Or [t2, t3])]) (Or [(And [t1, t2]), (And [t1, t3])])
    it "Or Idempotency" $ property $
      \t -> equiv (Or [t, t]) t
    it "And Idempotency" $ property $
      \t -> equiv (And [t, t]) t
    it "Tautology" $ property $
      \t -> equiv (Or [t, (Not t)]) Any
    it "Contradiction" $ property $
      \t -> equiv (And [t, (Not t)]) Empty
    it "Reflexivity" $ property $
      \t -> equiv t t
    it "Double Negation" $ property $
      \t -> equiv t (Not (Not t))
    it "DeMorgan's Law 1" $ property $
      \t1 t2 -> equiv (Not (Or [t1, t2])) (And [(Not t1), (Not t2)])
    it "DeMorgan's Law 2" $ property $
      \t1 t2 -> equiv (Not (And [t1, t2])) (Or [(Not t1), (Not t2)])
    it "Disjunctive Syllogism 1" $ property $
      \t1 t2 -> subtype (And [(Or [t1, t2]), (Not t1)]) t2
    it "Disjunctive Syllogism 2" $ property $
      \t1 t2 -> subtype (And [(Or [t1, t2]), (Not t2)]) t1


  describe "NAND tests" $ do
    it "NOT with NAND" $ property $
      \t -> equiv (Not t) (nand t t)
    it "AND with NAND" $ property $
      \t1 t2 -> equiv (And [t1,t2]) (nand (nand t1 t2) (nand t1 t2))
    it "OR with NAND" $ property $
      \t1 t2 -> equiv (Or [t1,t2]) (nand (nand t1 t1) (nand t2 t2))
    it "NOR with NAND" $ property $
      \t1 t2 -> (equiv
                 (Not (Or [t1,t2]))
                 (nand
                  (nand (nand t1 t1) (nand t2 t2))
                  (nand (nand t1 t1) (nand t2 t2))))
    it "XOR with NAND" $ property $
      \t1 t2 -> (equiv
                 (Or [(And [t1,(Not t2)]),(And [t2,(Not t1)])])
                 (nand
                  (nand t1 (nand t1 t2))
                  (nand t2 (nand t1 t2))))
    it "XNOR with NAND" $ property $
      \t1 t2 -> (equiv
                 (Or [(And [t1,t2]),(And [(Not t1),(Not t2)])])
                 (nand
                  (nand (nand t1 t1) (nand t2 t2))
                  (nand t1 t2)))
                
  where subtype :: Ty -> Ty -> Bool
        subtype t1 t2 = rawSubtype (parse t1) (parse t2)

        overlap :: Ty -> Ty -> Bool
        overlap t1 t2 = rawOverlap (parse t1) (parse t2)

        equiv :: Ty -> Ty -> Bool
        equiv t1 t2 = rawEquiv (parse t1) (parse t2)

        nand :: Ty -> Ty -> Ty
        nand t1 t2 = Not (And [t1, t2])



runSubtypeTests :: (Ty -> Ty -> Bool) -> [String]
runSubtypeTests subtype =
  if testResults == []
  then ["All tests passed!"]
  else (((show (length testResults))
         ++ " of "
         ++ (show (length basicSubtypeTests))
         ++ " tests failed!")
        : testResults)
  where
    testResults = reverse (foldl runSingleTest []
                           basicSubtypeTests)
    runSingleTest results (t1, t2, expected) =
      if (subtype t1 t2) == expected
      then results
      else failureMsg : results

      where failureMsg = ("Test failure: " ++ show (t1, t2, expected))


-- list of (T1, T2, Ans), i.e. we expect T1 <: T2 to be Ans
basicSubtypeTests :: [(Ty, Ty, Bool)]
basicSubtypeTests =
  -- base types
  [ ((Base T) , (Base T) , True)
  , ((Base F) , (Base F) , True)
  , ((Base Zero) , (Base Zero) , True)
  , ((Base T) , (Base F) , False)
  , ((Base F) , (Base T) , False)
  , ((Base T) , (Base F) , False)
  , ((Base F) , (Base T) , False)
  , ((Base F) , (Base Zero) , False)
  , ((Base T) , (Base Zero) , False)
  , ((Base Zero) , (Base F) , False)
  , ((Base Zero) , (Base T) , False)
  
  -- Any and Empty
  , (Empty , Any, True)
  , (Any , Empty, False)
  , (Empty , (Base T), True)
  , ((Base T) , Empty, False)
  , (Any , (Base T), False)
  , ((Base T) , Any, True)

  -- Prod
  , ((Prod Any Any) , (Prod Any Any) , True)
  , ((Prod Empty Any) , (Prod Any Any) , True)
  , ((Prod Any Empty) , (Prod Any Any) , True)
  , ((Prod Any Any) , (Prod Empty Any) , False)
  , ((Prod Any Any) , (Prod Any Empty) , False)
  , ((Prod (Base T) Any) , (Prod Any Any) , True)
  , ((Prod Any (Base T)) , (Prod Any Any) , True)
  , ((Prod (Base T) (Base T)) , (Prod Any Any) , True)
  , ((Prod Any Any) , (Prod (Base T) Any) , False)
  , ((Prod Any Any) , (Prod Any (Base T)) , False)
  , ((Prod Any Any) , (Prod (Base T) (Base T)) , False)

  -- Arrow
  , ((Arrow Any Any) , (Arrow Any Any) , True)
  , ((Arrow Empty Any) , (Arrow Any Any) , False)
  , ((Arrow Any Empty) , (Arrow Any Any) , True)
  , ((Arrow Any Any) , (Arrow Empty Any) , True)
  , ((Arrow Any Any) , (Arrow Empty (Base T)) , True)
  , ((Arrow Any Any) , (Arrow Any Empty) , False)
  , ((Arrow (Base T) Any) , (Arrow Any Any) , False)
  , ((Arrow Any (Base T)) , (Arrow Any Any) , True)
  , ((Arrow (Base T) (Base T)) , (Arrow Any Any) , False)
  , ((Arrow Any Any) , (Arrow (Base T) Any) , True)
  , ((Arrow Any Any) , (Arrow Any (Base T)) , False)
  , ((Arrow Any Any) , (Arrow (Base T) (Base T)) , False)
  , ((Arrow Empty Empty), Empty, False)
  , ((Arrow Empty Empty), Any, True)
  , ((Arrow Empty Any), (Arrow Empty Empty), True)
  , ((Arrow Empty Any), (Arrow Any Empty), False)
  , ((Arrow (Base Zero) (Base Zero)), (Arrow (Base Zero) Any), True)
  , ((Arrow Any (Base Zero)), (Arrow (Base Zero) Any), True)
  , ((Arrow (Base Zero) (Base Zero)), (Arrow Any (Base Zero)), False)
  , ((Arrow (Base Zero) Any), (Arrow (Base Zero) (Base Zero)), False)


  
  -- Or
  , ((Base T) , Or [(Base T), (Base F)], True)
  , ((Base F) , Or [(Base T), (Base F)], True)
  , (Or [(Base T), (Base F)], (Base T),  False)
  , (Or [(Base T), (Base F)], (Base F),  False)
  , (Or [(Base T), (Base F)] , Or [(Base T), (Base F) , (Base Zero)] , True)
  , (Or [(Base T), (Base F)] , Or [(Base T), (Base F) , (Base Zero)], True)
  , (Or [(Base T), (Base F) , (Base Zero)], Or [(Base T), (Base F)] , False)
  , ((Or [(Base Zero), (Base T), (Base F)]), Or [(Base T), (Base F)], False)


  -- Or + Prod
  , ((Prod (Base T) (Base T)) ,
     (Prod (Or [(Base T), (Base F)]) (Base T)) ,
     True)
  , ((Prod (Base T) (Base T)) ,
      (Prod (Base T) (Or [(Base T), (Base F)])) ,
      True)
  , ((Prod (Base T) (Base T)) ,
      (Prod (Or [(Base T), (Base F)]) (Or [(Base T), (Base F)])) ,
      True)
  , ((Or [(Prod (Base T) (Base T)), (Prod (Base T) (Base F)), (Prod (Base F) (Base T)), (Prod (Base F) (Base F))]) ,
      (Prod (Or [(Base T), (Base F)]) (Or [(Base T), (Base F)])) ,
      True)
  , ((Prod (Or [(Base T), (Base F)]) (Or [(Base T), (Base F)])) ,
     (Or [(Prod (Base T) (Base T)), (Prod (Base T) (Base F)), (Prod (Base F) (Base T)), (Prod (Base F) (Base F))]) ,
      True)
  , ((Or [(Prod (Or [(Base T), (Base F)]) (Base T)), (Prod (Or [(Base T), (Base F)]) (Base F))]) ,
      (Or [(Prod (Base T) (Base T)), (Prod (Base T) (Base F)), (Prod (Base F) (Base T)), (Prod (Base F) (Base F))]) ,
      True)
  , ((Or [(Prod (Base T) (Or [(Base T), (Base F)])), (Prod (Base F) (Or [(Base T), (Base F)]))]) ,
      (Or [(Prod (Base T) (Base T)), (Prod (Base T) (Base F)), (Prod (Base F) (Base T)), (Prod (Base F) (Base F))]) ,
      True)
  , ((Or [(Prod (Base T) (Base T)), (Prod (Base T) (Base F)), (Prod (Base F) (Base T)), (Prod (Base F) (Base F))]) ,
      (Or [(Prod (Or [(Base T), (Base F)]) (Base T)), (Prod (Or [(Base T), (Base F)]) (Base F))]) ,
      True)
  , ((Or [(Prod (Base T) (Base T)), (Prod (Base T) (Base F)), (Prod (Base F) (Base T)), (Prod (Base F) (Base F))]) ,
     (Or [(Prod (Base T) (Or [(Base T), (Base F)])), (Prod (Base F) (Or [(Base T), (Base F)]))]) ,
      True)
  , (Or [(Prod (Base T) (Base T)), (Prod (Base F) (Base F))],
     (Prod (Or [(Base T), (Base F)]) (Or [(Base T), (Base F)])),
     True)
  , ((Prod (Or [(Base T), (Base F)]) (Or [(Base T), (Base F)])),
     Or [(Prod (Base T) (Base T)), (Prod (Base F) (Base F))],
     False)

  -- Or + Arrow
  , (Or [(Arrow (Base T) (Base T)), (Arrow (Base F) (Base F))],
     (Arrow (Or [(Base T), (Base F)]) (Or [(Base T), (Base F)])),
     False)
  , ((Arrow (Or [(Base T), (Base F)]) (Or [(Base T), (Base F)])),
      Or [(Arrow (Base T) (Base T)), (Arrow (Base F) (Base F))],
      False)
  , ((Arrow (Or [(Base T), (Base F)]) (Or [(Base T), (Base F)])),
      Or [(Arrow (Base T) (Or [(Base T), (Base F)])),
           (Arrow (Base F) (Or [(Base T), (Base F)]))],
      True)
  , ((Or [(Arrow (Or [(Base T), (Base F)]) (Or [(Base T), (Base F)])),
          (Arrow (Or [(Base T), (Base Zero)]) (Or [(Base T), (Base F)]))]),
     (Arrow (Base T) (Or [(Base T), (Base F)])),
      True)
    
  -- And
  , ((Base T) , And [(Base T), (Base F)], False)
  , (And [(Base T), (Base F)], (Base T) , True)
  , (And [(Or [(Base T), (Base F)]), (Or [(Base T), (Base Zero)])], (Base T) , True)
  , (And [(Or [(Base T), (Base F)]), (Or [(Base T), (Base Zero)])], (Base F) , False)
  , ((Base T) , And [(Or [(Base T), (Base F)]), (Or [(Base T), (Base Zero)])], True)
  , ((Base T) , And [(Or [(Base T), (Base F)]), (Or [(Base T), (Base Zero)])], True)
  , (And [(Arrow (Base T) (Base T)), (Arrow (Base F) (Base F))],
     Arrow (Or [(Base T), (Base F)]) (Or [(Base T), (Base F)]),
     True)
  , (And [(Arrow (Base T) (Base T)), (Prod (Base F) (Base F))],
      Empty,
      True)
  , (And [(Prod (Base T) Any), (Prod Any (Base T))],
     (Prod (Base T) (Base T)),
     True)
    , (And [(Prod (Or [(Base T), (Base F)]) (Base T)),
            (Prod (Base T) (Or [(Base T), (Base F)]))],
     (Prod (Base T) (Base T)),
     True)
      
  -- Not
    , (Not Any, Empty, True)
    , (Not Empty, Empty, False)
    , (Not Empty, Any, True)
    , (Not (Or [(Base T), (Base F)]), (Not (Base T)), True)
    , ((Not (Base T)), Not (Or [(Base T), (Base F)]), False)
    , (Not (Not (Base T)), (Base T), True)
    , (And [(Prod (Or [(Base T), (Base F)])
             (Or [(Base T), (Base F)])),
            (Not (Prod (Base F) (Base F)))],
        (Prod (Base T) (Base T)),
        False)

    , ((Prod (Base Zero) (Base Zero)), (Prod Any Any), True)
    , ((Prod Empty (Base Zero)), (Prod (Base Zero) (Base Zero)), True)
    , ((Prod (Base Zero) Empty), (Prod (Base Zero) (Base Zero)), True)
    , ((Prod (Base Zero) (Base Zero)), (Prod (Base Zero) Any), True)
    , ((Prod (Base Zero) (Base Zero)), (Prod Any (Base Zero)), True)
    , ((Prod (Base Zero) (Base Zero)), (Prod (Base Zero) (Base Zero)), True)
    , ((Prod (Base Zero) (Base Zero)), (Prod Empty (Base Zero)), False)
    , ((Prod (Base Zero) (Base Zero)), (Prod (Base Zero) Empty), False)
    , ((Prod (Base Zero) (Base Zero)), (Prod Empty Empty), False)
    , ((Prod (Base Zero) (Base Zero)), (Prod (Or [(Base T),(Base F)]) (Base Zero)), False)
    , ((Prod (Base Zero) (Base Zero)), (Prod (Base Zero) (Or [(Base T),(Base F)])), False)
    , ((Prod (Base Zero) (Base Zero)), (Prod (Or [(Base Zero), (Base T),(Base F)]) (Base Zero)), True)
      
    -- misc
    , ((And [(Or [(Base T), (Base F)]), (Not (Base T))]) , (Base F) , True)
    , ((Base F) , (And [(Or [(Base T), (Base F)]), (Not (Base T))]) , True)
    , ((Base F) , (And [(Not (Base T)), (Or [(Base T), (Base F)])]) , True)

    , ((And [(Or [(Prod (Base T) (Base T)), (Prod (Base T) (Base F)), (Prod (Base F) (Base T)), (Prod (Base F) (Base F))]),
             (Not (Prod (Base T) Any))]) ,
       (Or [(Prod (Base F) (Base T)), (Prod (Base F) (Base F))]) ,
       True)
    , ((And [(Or [(Prod (Base T) (Base T)), (Prod (Base T) (Base F)), (Prod (Base F) (Base T)), (Prod (Base F) (Base F))]),
             (Prod (Not (Base T)) (Or [(Base Zero), (Base T),(Base F)]))]) ,
       (Or [(Prod (Base F) (Base T)), (Prod (Base F) (Base F))]) ,
       True)
    , ((Or [(Prod (Base F) (Base T)), (Prod (Base F) (Base F))]),
       (Or [(Prod (Base T) (Base T)), (Prod (Base T) (Base F)), (Prod (Base F) (Base T)), (Prod (Base F) (Base F))]),
       True)
    , ((Or [(Prod (Base F) (Base T)), (Prod (Base F) (Base F))]) ,
       (And [(Or [(Prod (Base T) (Base T)), (Prod (Base T) (Base F)), (Prod (Base F) (Base T)), (Prod (Base F) (Base F))]),
             (Prod (Not (Base T)) (Or [(Base Zero), (Base T),(Base F)]))]) ,
       True)


      -- Recursive Type Tests
    , (Name "NumList", Name "IntList", False)
    , (Name "IntList", Name "NumList", True)
    , (And [(Name "IntList"), (Not (Name "NumList"))], Empty, True)
    , (And [(Name "IntList"), (Name "NumList")], (Name "NumList"), True)
    , ((Name "NumList"), And [(Name "IntList"), (Name "NumList")], False)
    , (And [(Name "NumList"), (Not (Name "IntList"))], (Name "NumList"), True)
    
  ]
