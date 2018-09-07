module Types.MetafunctionTests (genMetafunctionSpec) where


import Test.Hspec
import Test.QuickCheck
import Types.Syntax
import qualified Types.LazyBDD as BDD
import Types.BaseEnv


genMetafunctionSpec ::
  (Ty -> BDD.Ty)
  -> (BDD.Ty -> BDD.Ty -> Bool)
  -> (BDD.Ty -> BDD.Ty -> Bool)
  -> (BDD.Ty -> BDD.Ty -> Bool)
  -> (BDD.Ty -> Maybe BDD.Ty)
  -> (BDD.Ty -> Maybe BDD.Ty)
  -> (BDD.Ty -> Maybe BDD.Ty)
  -> (BDD.Ty -> BDD.Ty -> Maybe BDD.Ty)
  -> (BDD.Ty -> BDD.Ty -> BDD.Ty -> Maybe BDD.Ty)
  -> Spec
genMetafunctionSpec
  parse
  rawSubtype
  rawOverlap
  rawEquiv
  rawFstProj
  rawSndProj
  rawDomTy
  rawRngTy
  rawInTy = do
  describe "First Projection Tests" $ do
    it "Projection from Empty 1" $ do
      fstProjEquiv Empty Empty `shouldBe` True
    it "Projection from Empty 2" $ do
      fstProjEquiv (And [Prod (Or [Base T, Base Zero]) (Base F), Not (Prod (Base Zero) Any)]) (Base T)
        `shouldBe` True
    it "Simple Pair" $ property $
      \t -> fstProjEquiv (Prod t Any) t
    it "Union of Pairs" $ property $
      \t1 t2 -> (fstProjEquiv
                 (Or [(Prod t1 Any), (Prod t2 Any)])
                 (Or [t1, t2]))
    it "Intersection of Pairs" $ property $
      \t1 t2 -> (fstProjEquiv
                 (And [(Prod t1 Any), (Prod t2 Any)])
                 (And [t1, t2]))
    it "Intersection of Union of Pairs1" $ property $
      \t1 t2 t3 t4 ->
        (fstProjEquiv
         (And [(Or [(Prod t1 Any), (Prod t2 Any)]),
               (Or [(Prod t3 Any), (Prod t4 Any)])])
          (And [(Or [t1, t2]),
                (Or [t3, t4])]))
    it "Intersection of Union of Pairs2" $ property $
      \t1 t2 t3 t4 t5 t6 t7 t8 ->
        (fstProjSubtype
         (And [(Or [(Prod t1 t2), (Prod t3 t4)]),
               (Or [(Prod t5 t6), (Prod t7 t8)])])
         (And [(Or [t1, t3]),
               (Or [t5, t7])]))
    it "Union of Intersection of Pairs1" $ property $
      \t1 t2 t3 t4 ->
        (fstProjEquiv
         (Or [(And [(Prod t1 Any), (Prod t2 Any)]),
              (And [(Prod t3 Any), (Prod t4 Any)])])
          (Or [(And [t1, t2]),
               (And [t3, t4])]))
    it "Union of Intersection of Pairs2" $ property $
      \t1 t2 t3 t4 t5 t6 t7 t8 ->
        (fstProjSubtype
         (Or [(And [(Prod t1 t2), (Prod t3 t4)]),
              (And [(Prod t5 t6), (Prod t7 t8)])])
          (Or [(And [t1, t3]),
               (And [t5, t7])]))

  describe "Second Projection Tests" $ do
    it "Projection from Empty 1" $ do
      (sndProjEquiv Empty Empty) `shouldBe` True
    it "Projection from Empty 2" $ do
      (sndProjEquiv (And [Prod (Base F) (Or [Base T, Base Zero]), Not (Prod Any (Base Zero))]) (Base T))
        `shouldBe`
        True
    it "Simple Pair" $ property $
      \t -> sndProjEquiv (Prod Any t) t
    it "Union of Pairs" $ property $
      \t1 t2 -> sndProjEquiv (Or [(Prod Any t1), (Prod Any t2)]) (Or [t1, t2])
    it "Intersection of Pairs" $ property $
      \t1 t2 -> sndProjEquiv (And [(Prod Any t1), (Prod Any t2)]) (And [t1, t2])
    it "Intersection of Union of Pairs1" $ property $
      \t1 t2 t3 t4 ->
        (sndProjEquiv
         (And [(Or [(Prod Any t1), (Prod Any t2)]),
               (Or [(Prod Any t3), (Prod Any t4)])])
          (And [(Or [t1, t2]),
                (Or [t3, t4])]))
    it "Intersection of Union of Pairs2" $ property $
      \t1 t2 t3 t4 t5 t6 t7 t8 ->
        (sndProjSubtype
         (And [(Or [(Prod t1 t2), (Prod t3 t4)]),
               (Or [(Prod t5 t6), (Prod t7 t8)])])
         (And [(Or [t2, t4]),
               (Or [t6, t8])]))
    it "Union of Intersection of Pairs1" $ property $
      \t1 t2 t3 t4 ->
        (sndProjEquiv
         (Or [(And [(Prod Any t1), (Prod Any t2)]),
              (And [(Prod Any t3), (Prod Any t4)])])
          (Or [(And [t1, t2]),
               (And [t3, t4])]))
    it "Union of Intersection of Pairs2" $ property $
      \t1 t2 t3 t4 t5 t6 t7 t8 ->
        (sndProjSubtype
         (Or [(And [(Prod t1 t2), (Prod t3 t4)]),
              (And [(Prod t5 t6), (Prod t7 t8)])])
          (Or [(And [t2, t4]),
               (And [t6, t8])]))

  describe "Function Domain Tests" $ do
    it "Simple Arrow" $ property $
      \t1 t2 -> domTyEquiv (Arrow t1 t2) t1
    it "Arrow Intersection" $ property $
      \t1 t2 t3 t4 -> (domTyEquiv
                       (And [(Arrow t1 t2),
                             (Arrow t3 t4)])
                        (Or [t1, t3]))
    it "Arrow Union" $ property $
      \t1 t2 t3 t4 -> (domTyEquiv
                       (Or [(Arrow t1 t2),
                            (Arrow t3 t4)])
                        (And [t1, t3]))

  describe "Function Range Tests" $ do
    it "Simple Arrow1" $ do
      (rngTyEquiv (Arrow (Base T) (Base F)) (Base T) (Base F) `shouldBe` True)
    it "Simple Arrow2" $ do
      (rngTyEquiv
       (And [(Arrow (Or [(Base T), (Base F)]) (Base F)),
             (Arrow (Or [(Base T), (Base Zero)]) (Base F))])
       (Base T)
       (Base F)
        `shouldBe`
        True)
    it "Simple Arrow3" $ do
      (rngTyEquiv
       (And [(Arrow (Or [(Base T), (Base F)]) (Or [(Base T), (Base F)])),
             (Arrow (Or [(Base T), (Base Zero)]) (Or [(Base Zero), (Base F)]))])
       (Base T)
       (Base F)
        `shouldBe`
        True)
    it "Simple Arrow4" $ do
      (rngTyEquiv
       (And [(Arrow (Or [(Base T), (Base F)]) (Or [(Base T), (Base F)])),
             (Arrow (Or [(Base T), (Base Zero)]) (Or [(Base Zero), (Base F)])),
             (Arrow (Or [(Base F), (Base Zero)]) (Base T))])
       (Base T)
       (Base F)
        `shouldBe`
        True)
        -- TODO add more

  describe "Input Type Tests" $ do
    it "Simple Arrow 1a" $ do
      (inTyEquiv (Arrow (Base T) (Base F))
       (Base T) (Base F) (Base T) `shouldBe` True)
    it "Simple Arrow 1b" $ do
      (inTyEquiv (Arrow (Base T) (Base F))
       (Base T) (Not (Base F)) (Or []) `shouldBe` True)
    it "Arrow Intersection 1" $ do
      (inTyEquiv (And [(Arrow (Not (Base F)) (Base F)), (Arrow (Base F) (Base T))]) 
       Any (Base T) (Base F) `shouldBe` True)
    it "Arrow Intersection 2" $ do
      (inTyEquiv (And [(Arrow (Not (Base F)) (Base F)), (Arrow (Base F) (Base T))])
       Any (Not (Base F)) (Base F) `shouldBe` True)
    it "Arrow Intersection 3" $ do
      (inTyEquiv (And [(Arrow (Not (Base F)) (Base F)), (Arrow (Base F) (Base T))])
       Any (Base F) (Not (Base F)) `shouldBe` True)
    it "Arrow Intersection 4a" $ do
      (inTyEquiv (And [(Arrow (Base T) (Base F)), (Arrow (Base F) (Base T)), (Arrow (Base Zero) (Base One))])
       (Or [(Base T), (Base F), (Base Zero)]) (Not (Base F)) (Or [(Base F), (Base Zero)]) `shouldBe` True)
    it "Arrow Intersection 4b" $ do
      (inTyEquiv (And [(Arrow (Base T) (Base F)), (Arrow (Base F) (Base T)), (Arrow (Base Zero) (Base One))])
       (Or [(Base T), (Base F)]) (Not (Base F)) (Base F) `shouldBe` True)
    it "Arrow Intersection 5" $ do
      (inTyEquiv (And [(Arrow (Base T) (Base F)), (Arrow (Base F) (Base T)), (Arrow (Base Zero) (Base One))])
       (Or [(Base T), (Base F), (Base Zero)]) (Base F) (Base T) `shouldBe` True)
    it "Arrow Intersection 6a" $ do
      (inTyEquiv (Or [(And [(Arrow (Base T) (Base F)), (Arrow (Base F) (Base T)), (Arrow (Base Zero) (Base One))]),
                     (And [(Arrow (Base F) (Base F)), (Arrow (Base T) (Base T)), (Arrow (Base Zero) (Base One))])])
                  (Or [(Base T), (Base F), (Base Zero)]) (Base F) (Or [(Base T),(Base F)])
                  `shouldBe` True)
    it "Arrow Intersection 6b" $ do
      (inTyEquiv (Or [(And [(Arrow (Base T) (Base F)), (Arrow (Base F) (Base T)), (Arrow (Base Zero) (Base One))]),
                     (And [(Arrow (Base F) (Base F)), (Arrow (Base T) (Base T)), (Arrow (Base Zero) (Base One))])])
                  (Or [(Base T),(Base Zero)]) (Base F) (Base T)
                  `shouldBe` True)
    it "Arrow Intersection 7a" $ do
      (inTyEquiv (Or [(And [(Arrow (Base T) (Base F)), (Arrow (Base F) (Base T)), (Arrow (Base Zero) (Base One))]),
                     (And [(Arrow (Base F) (Base F)), (Arrow (Base T) (Base T)), (Arrow (Base Zero) (Base One))])])
                  (Or [(Base T), (Base F), (Base Zero)]) (Not (Base F)) (Or [(Base Zero), (Base T), (Base F)])
                  `shouldBe` True)
    it "Arrow Intersection 7b" $ do
      (inTyEquiv (Or [(And [(Arrow (Base T) (Base F)), (Arrow (Base F) (Base T)), (Arrow (Base Zero) (Base One))]),
                     (And [(Arrow (Base F) (Base F)), (Arrow (Base T) (Base T)), (Arrow (Base Zero) (Base One))])])
                  (Or [(Base T), (Base F)]) (Not (Base F)) (Or [(Base T), (Base F)])
                  `shouldBe` True)
    it "inTyCases 1" $ property $
      \t1 t2 t3 -> (inTyCases (Arrow t1 t2) t3)
    it "inTyCases 2" $ property $
      \t1 t2 t3 t4 t5 -> (inTyCases (And [(Arrow t1 t2), (Arrow t3 t4)]) t5)
    it "inTyCases 3" $ property $
      \t1 t2 t3 t4 t5 t6 t7 t8 t9 ->
        (inTyCases
         (Or [(And [(Arrow t1 t2), (Arrow t3 t4)]),
              (And [(Arrow t5 t6), (Arrow t7 t8)])])
         t9)
        

    where fstProjEquiv :: Ty -> Ty -> Bool
          fstProjEquiv rawt1 rawt2 =
            case (rawFstProj t1) of
              Nothing  -> False
              Just t1' -> rawEquiv t1' t2
            where t1 = (parse rawt1)
                  t2 = (parse rawt2)

          fstProjSubtype :: Ty -> Ty -> Bool
          fstProjSubtype rawt1 rawt2 =
            case (rawFstProj t1) of
              Nothing  -> False
              Just t1' -> rawSubtype t1' t2
            where t1 = (parse rawt1)
                  t2 = (parse rawt2)

          sndProjEquiv :: Ty -> Ty -> Bool
          sndProjEquiv rawt1 rawt2 =
            case (rawSndProj t1) of
              Nothing -> False
              Just t1' -> rawEquiv t1' t2
            where t1 = (parse rawt1)
                  t2 = (parse rawt2)

          sndProjSubtype :: Ty -> Ty -> Bool
          sndProjSubtype rawt1 rawt2 =
            case (rawSndProj t1) of
              Nothing  -> False
              (Just t1') -> rawSubtype t1' t2
            where t1 = (parse rawt1)
                  t2 = (parse rawt2)

          domTyEquiv :: Ty -> Ty -> Bool
          domTyEquiv rawt1 rawt2 =
            case (rawDomTy t1) of
              Nothing  -> False
              Just t1' -> rawEquiv t1' t2
            where t1 = (parse rawt1)
                  t2 = (parse rawt2)

          rngTyEquiv :: Ty -> Ty -> Ty -> Bool
          rngTyEquiv rawt1 rawargty rawt2 =
            case (rawRngTy t1 argty) of
              Nothing  -> False
              Just t1' -> rawEquiv t1' t2
            where t1 = (parse rawt1)
                  argty = (parse rawargty)
                  t2 = (parse rawt2)


          inTyEquiv :: Ty -> Ty -> Ty -> Ty -> Bool
          inTyEquiv rawt1 rawargty rawoutty rawt2 =
            case (rawInTy t1 argty outty) of
              Nothing  -> False
              Just t1' -> rawEquiv t1' t2
            where t1 = (parse rawt1)
                  argty = (parse rawargty)
                  outty = (parse rawoutty)
                  t2 = (parse rawt2)


          inTyCases :: Ty -> Ty -> Bool
          inTyCases rawtfunty rawargty =
            case ((rawRngTy funty argty),
                  (rawInTy funty argty nonFalseTy),
                  (rawInTy funty argty falseTy)) of
              (Just resty, Just posty, Just negty) ->
                -- verify anything not covered by posty union negty
                -- is mapped to empty
                (case (rawRngTy funty (BDD.tyDiff argty (BDD.tyOr posty negty))) of
                    Nothing -> False
                    Just rng -> (rawSubtype rng BDD.emptyTy))
                &&
                -- if the result is calculated to be empty, then it
                -- should not be included in either of our input
                -- type predictions
                (if (rawSubtype resty BDD.emptyTy)
                 then (not ((rawOverlap argty posty)
                            || (rawOverlap argty negty)))
                  -- if the result of function application is some non-empty,
                  -- non-false value, then any part of the argument's type
                  -- outside of our predicted positive input type calculation
                  -- should be mapped to bottom
                 else if (rawSubtype resty nonFalseTy)
                 then ((not (rawOverlap argty negty))
                       && (case (rawRngTy funty (BDD.tyDiff argty posty)) of
                             Nothing -> False
                             Just rng -> (rawSubtype rng BDD.emptyTy)))
                  -- if the result of function application is false,
                  -- then any part of the argument's type outside of our
                  -- predicted negative input type calculation
                  -- should be mapped to bottom
                 else if (rawSubtype resty falseTy)
                 then ((not (rawOverlap argty posty))
                       && (case (rawRngTy funty (BDD.tyDiff argty negty)) of
                             Nothing -> False
                             Just rng -> (rawSubtype rng BDD.emptyTy)))
                  -- otherwise we know the output is non-empty and
                  -- includes false and non-false values, so it
                  -- must overlap with both posty and negty
                  else ((rawOverlap argty posty) && (rawOverlap argty negty)))
              _ -> True
            where nonFalseTy = (parse (Not (Base F)))
                  falseTy = (parse (Base F))
                  funty = (parse rawtfunty)
                  argty = (parse rawargty)
