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
      \t1 t2 -> not (overlap T (Prod t1 t2))
    it "Base/Arrow disjoint" $ property $
      \t1 t2 -> not (overlap T (Arrow t1 t2))
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
  [ (T , T , True)
  , (F , F , True)
  , (Zero , Zero , True)
  , (T , F , False)
  , (F , T , False)
  , (T , F , False)
  , (F , T , False)
  , (F , Zero , False)
  , (T , Zero , False)
  , (Zero , F , False)
  , (Zero , T , False)
  
  -- Any and Empty
  , (Empty , Any, True)
  , (Any , Empty, False)
  , (Empty , T, True)
  , (T , Empty, False)
  , (Any , T, False)
  , (T , Any, True)

  -- Prod
  , ((Prod Any Any) , (Prod Any Any) , True)
  , ((Prod Empty Any) , (Prod Any Any) , True)
  , ((Prod Any Empty) , (Prod Any Any) , True)
  , ((Prod Any Any) , (Prod Empty Any) , False)
  , ((Prod Any Any) , (Prod Any Empty) , False)
  , ((Prod T Any) , (Prod Any Any) , True)
  , ((Prod Any T) , (Prod Any Any) , True)
  , ((Prod T T) , (Prod Any Any) , True)
  , ((Prod Any Any) , (Prod T Any) , False)
  , ((Prod Any Any) , (Prod Any T) , False)
  , ((Prod Any Any) , (Prod T T) , False)

  -- Arrow
  , ((Arrow Any Any) , (Arrow Any Any) , True)
  , ((Arrow Empty Any) , (Arrow Any Any) , False)
  , ((Arrow Any Empty) , (Arrow Any Any) , True)
  , ((Arrow Any Any) , (Arrow Empty Any) , True)
  , ((Arrow Any Any) , (Arrow Empty T) , True)
  , ((Arrow Any Any) , (Arrow Any Empty) , False)
  , ((Arrow T Any) , (Arrow Any Any) , False)
  , ((Arrow Any T) , (Arrow Any Any) , True)
  , ((Arrow T T) , (Arrow Any Any) , False)
  , ((Arrow Any Any) , (Arrow T Any) , True)
  , ((Arrow Any Any) , (Arrow Any T) , False)
  , ((Arrow Any Any) , (Arrow T T) , False)
  , ((Arrow Empty Empty), Empty, False)
  , ((Arrow Empty Empty), Any, True)
  , ((Arrow Empty Any), (Arrow Empty Empty), True)
  , ((Arrow Empty Any), (Arrow Any Empty), False)
  , ((Arrow Zero Zero), (Arrow Zero Any), True)
  , ((Arrow Any Zero), (Arrow Zero Any), True)
  , ((Arrow Zero Zero), (Arrow Any Zero), False)
  , ((Arrow Zero Any), (Arrow Zero Zero), False)


  
  -- Or
  , (T , Or [T, F], True)
  , (F , Or [T, F], True)
  , (Or [T, F], T,  False)
  , (Or [T, F], F,  False)
  , (Or [T, F] , Or [T, F , Zero] , True)
  , (Or [T, F] , Or [T, F , Zero], True)
  , (Or [T, F , Zero], Or [T, F] , False)
  , ((Or [Zero, T, F]), Or [T, F], False)


  -- Or + Prod
  , ((Prod T T) ,
     (Prod (Or [T, F]) T) ,
     True)
  , ((Prod T T) ,
      (Prod T (Or [T, F])) ,
      True)
  , ((Prod T T) ,
      (Prod (Or [T, F]) (Or [T, F])) ,
      True)
  , ((Or [(Prod T T), (Prod T F), (Prod F T), (Prod F F)]) ,
      (Prod (Or [T, F]) (Or [T, F])) ,
      True)
  , ((Prod (Or [T, F]) (Or [T, F])) ,
     (Or [(Prod T T), (Prod T F), (Prod F T), (Prod F F)]) ,
      True)
  , ((Or [(Prod (Or [T, F]) T), (Prod (Or [T, F]) F)]) ,
      (Or [(Prod T T), (Prod T F), (Prod F T), (Prod F F)]) ,
      True)
  , ((Or [(Prod T (Or [T, F])), (Prod F (Or [T, F]))]) ,
      (Or [(Prod T T), (Prod T F), (Prod F T), (Prod F F)]) ,
      True)
  , ((Or [(Prod T T), (Prod T F), (Prod F T), (Prod F F)]) ,
      (Or [(Prod (Or [T, F]) T), (Prod (Or [T, F]) F)]) ,
      True)
  , ((Or [(Prod T T), (Prod T F), (Prod F T), (Prod F F)]) ,
     (Or [(Prod T (Or [T, F])), (Prod F (Or [T, F]))]) ,
      True)
  , (Or [(Prod T T), (Prod F F)],
     (Prod (Or [T, F]) (Or [T, F])),
     True)
  , ((Prod (Or [T, F]) (Or [T, F])),
     Or [(Prod T T), (Prod F F)],
     False)

  -- Or + Arrow
  , (Or [(Arrow T T), (Arrow F F)],
     (Arrow (Or [T, F]) (Or [T, F])),
     False)
  , ((Arrow (Or [T, F]) (Or [T, F])),
      Or [(Arrow T T), (Arrow F F)],
      False)
  , ((Arrow (Or [T, F]) (Or [T, F])),
      Or [(Arrow T (Or [T, F])),
           (Arrow F (Or [T, F]))],
      True)
  , ((Or [(Arrow (Or [T, F]) (Or [T, F])),
          (Arrow (Or [T, Zero]) (Or [T, F]))]),
     (Arrow T (Or [T, F])),
      True)
    
  -- And
  , (T , And [T, F], False)
  , (And [T, F], T , True)
  , (And [(Or [T, F]), (Or [T, Zero])], T , True)
  , (And [(Or [T, F]), (Or [T, Zero])], F , False)
  , (T , And [(Or [T, F]), (Or [T, Zero])], True)
  , (T , And [(Or [T, F]), (Or [T, Zero])], True)
  , (And [(Arrow T T), (Arrow F F)],
     Arrow (Or [T, F]) (Or [T, F]),
     True)
  , (And [(Arrow T T), (Prod F F)],
      Empty,
      True)
  , (And [(Prod T Any), (Prod Any T)],
     (Prod T T),
     True)
    , (And [(Prod (Or [T, F]) T),
            (Prod T (Or [T, F]))],
     (Prod T T),
     True)
      
  -- Not
    , (Not Any, Empty, True)
    , (Not Empty, Empty, False)
    , (Not Empty, Any, True)
    , (Not (Or [T, F]), (Not T), True)
    , ((Not T), Not (Or [T, F]), False)
    , (Not (Not T), T, True)
    , (And [(Prod (Or [T, F])
             (Or [T, F])),
            (Not (Prod F F))],
        (Prod T T),
        False)

    , ((Prod Zero Zero), (Prod Any Any), True)
    , ((Prod Empty Zero), (Prod Zero Zero), True)
    , ((Prod Zero Empty), (Prod Zero Zero), True)
    , ((Prod Zero Zero), (Prod Zero Any), True)
    , ((Prod Zero Zero), (Prod Any Zero), True)
    , ((Prod Zero Zero), (Prod Zero Zero), True)
    , ((Prod Zero Zero), (Prod Empty Zero), False)
    , ((Prod Zero Zero), (Prod Zero Empty), False)
    , ((Prod Zero Zero), (Prod Empty Empty), False)
    , ((Prod Zero Zero), (Prod (Or [T,F]) Zero), False)
    , ((Prod Zero Zero), (Prod Zero (Or [T,F])), False)
    , ((Prod Zero Zero), (Prod (Or [Zero, T,F]) Zero), True)
      
    -- misc
    , ((And [(Or [T, F]), (Not T)]) , F , True)
    , (F , (And [(Or [T, F]), (Not T)]) , True)
    , (F , (And [(Not T), (Or [T, F])]) , True)

    , ((And [(Or [(Prod T T), (Prod T F), (Prod F T), (Prod F F)]),
             (Not (Prod T Any))]) ,
       (Or [(Prod F T), (Prod F F)]) ,
       True)
    , ((And [(Or [(Prod T T), (Prod T F), (Prod F T), (Prod F F)]),
             (Prod (Not T) (Or [Zero, T,F]))]) ,
       (Or [(Prod F T), (Prod F F)]) ,
       True)
    , ((Or [(Prod F T), (Prod F F)]),
       (Or [(Prod T T), (Prod T F), (Prod F T), (Prod F F)]),
       True)
    , ((Or [(Prod F T), (Prod F F)]) ,
       (And [(Or [(Prod T T), (Prod T F), (Prod F T), (Prod F F)]),
             (Prod (Not T) (Or [Zero, T,F]))]) ,
       True)
    
  ]
