module Types.MetafunctionTests (genMetafunctionSpec) where


import Test.Hspec
import Test.QuickCheck
import Types.Syntax
import qualified Types.LazyBDD as Impl


genMetafunctionSpec ::
  (Ty -> Impl.Ty)
  -> (Impl.Ty -> Impl.Ty -> Bool)
  -> (Impl.Ty -> Impl.Ty -> Bool)
  -> (Impl.Ty -> Impl.Ty -> Bool)
  -> (Impl.Ty -> Maybe Impl.Ty)
  -> (Impl.Ty -> Maybe Impl.Ty)
  -> (Impl.Ty -> Maybe Impl.Ty)
  -> (Impl.Ty -> Impl.Ty -> Maybe Impl.Ty)
  -> (Impl.Ty -> Impl.Ty -> Maybe Impl.Ty)
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
      fstProjEquiv (And [Prod (Or [T,Zero]) F,Not (Prod Zero Any)]) T `shouldBe` True
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
      (sndProjEquiv (And [Prod F (Or [T,Zero]),Not (Prod Any Zero)]) T)
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
      (rngTyEquiv (Arrow T F) T F `shouldBe` True)
    it "Simple Arrow2" $ do
      (rngTyEquiv
       (And [(Arrow (Or [T, F]) F),
             (Arrow (Or [T, Zero]) F)])
       T
       F
        `shouldBe`
        True)
    it "Simple Arrow3" $ do
      (rngTyEquiv
       (And [(Arrow (Or [T, F]) (Or [T, F])),
             (Arrow (Or [T, Zero]) (Or [Zero, F]))])
       T
       F
        `shouldBe`
        True)
    it "Simple Arrow4" $ do
      (rngTyEquiv
       (And [(Arrow (Or [T, F]) (Or [T, F])),
             (Arrow (Or [T, Zero]) (Or [Zero, F])),
             (Arrow (Or [F, Zero]) T)])
       T
       F
        `shouldBe`
        True)
        -- TODO add more

  describe "Input Type Tests" $ do
    it "Simple Arrow1" $ do
      (inTyEquiv (Arrow T F) F T `shouldBe` True)
    it "Simple Arrow1" $ do
      (inTyEquiv (Arrow T F) (Not F) (Or []) `shouldBe` True)
    it "Arrow Intersection 1" $ do
      (inTyEquiv (And [(Arrow (Not F) F), (Arrow F T)]) T F `shouldBe` True)
    it "Arrow Intersection 2" $ do
      (inTyEquiv (And [(Arrow (Not F) F), (Arrow F T)]) (Not F) F `shouldBe` True)
    it "Arrow Intersection 3" $ do
      (inTyEquiv (And [(Arrow (Not F) F), (Arrow F T)]) F (Not F) `shouldBe` True)
    it "Arrow Intersection 4" $ do
      (inTyEquiv (And [(Arrow T F), (Arrow F T), (Arrow Zero One)]) (Not F) (Or [F, Zero]) `shouldBe` True)
    it "Arrow Intersection 5" $ do
      (inTyEquiv (And [(Arrow T F), (Arrow F T), (Arrow Zero One)]) F T `shouldBe` True)
    it "Arrow Intersection 6" $ do
      (inTyEquiv (Or [(And [(Arrow T F), (Arrow F T), (Arrow Zero One)]),
                     (And [(Arrow F F), (Arrow T T), (Arrow Zero One)])])
                  F (Or [T,F])
                  `shouldBe` True)
    it "Arrow Intersection 7" $ do
      (inTyEquiv (Or [(And [(Arrow T F), (Arrow F T), (Arrow Zero One)]),
                     (And [(Arrow F F), (Arrow T T), (Arrow Zero One)])])
                  (Not F) (Or [Zero, T, F])
                  `shouldBe` True)
    it "inTyDisjoint 1" $ property $
      \t1 t2 -> (inTyDisjoint (Arrow t1 t2))
    it "inTyDisjoint 2" $ property $
      \t1 t2 t3 t4 -> (inTyDisjoint (And [(Arrow t1 t2), (Arrow t3 t4)]))
    it "inTyDisjoint 3" $ property $
      \t1 t2 t3 t4 t5 t6 t7 t8 ->
        (inTyDisjoint (Or [(And [(Arrow t1 t2), (Arrow t3 t4)]),
                           (And [(Arrow t5 t6), (Arrow t7 t8)])]))
    it "inTyTrue 1" $ property $
      \t1 t2 -> (inTyTrue (Arrow t1 t2))
    it "inTyTrue 2" $ property $
      \t1 t2 t3 t4 -> (inTyTrue (And [(Arrow t1 t2), (Arrow t3 t4)]))
    it "inTyTrue 3" $ property $
      \t1 t2 t3 t4 t5 t6 t7 t8 ->
        (inTyTrue (Or [(And [(Arrow t1 t2), (Arrow t3 t4)]),
                       (And [(Arrow t5 t6), (Arrow t7 t8)])]))
    it "inTyFalse 1" $ property $
      \t1 t2 -> (inTyFalse (Arrow t1 t2))
    it "inTyFalse 2" $ property $
      \t1 t2 t3 t4 -> (inTyFalse (And [(Arrow t1 t2), (Arrow t3 t4)]))
    it "inTyFalse 3" $ property $
      \t1 t2 t3 t4 t5 t6 t7 t8 ->
        (inTyFalse (Or [(And [(Arrow t1 t2), (Arrow t3 t4)]),
                        (And [(Arrow t5 t6), (Arrow t7 t8)])]))
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


          inTyEquiv :: Ty -> Ty -> Ty -> Bool
          inTyEquiv rawt1 rawargty rawt2 =
            case (rawInTy t1 argty) of
              Nothing  -> False
              Just t1' -> rawEquiv t1' t2
            where t1 = (parse rawt1)
                  argty = (parse rawargty)
                  t2 = (parse rawt2)

          inTyDisjoint :: Ty -> Bool
          inTyDisjoint rawfunty =
            case ((rawInTy funty false), (rawInTy funty nonFalse))  of
              (Just neg, Just pos) -> not (rawOverlap neg pos) 
              _ -> True
            where funty = (parse rawfunty)
                  false = (parse F)
                  nonFalse = (parse (Not F))

          inTyTrue :: Ty -> Bool
          inTyTrue rawfunty =
            case (rawInTy funty nonFalse) of
              Nothing  -> True
              Just truthy ->
                case (rawRngTy funty truthy) of
                  Nothing -> False
                  Just res -> (rawSubtype res nonFalse)
            where funty = (parse rawfunty)
                  nonFalse = (parse (Not F))

          inTyFalse :: Ty -> Bool
          inTyFalse rawfunty =
            case (rawInTy funty false) of
              Nothing  -> True
              Just falsy ->
                case (rawRngTy funty falsy) of
                  Nothing -> False
                  Just res -> (rawSubtype res false)
            where funty = (parse rawfunty)
                  false = (parse F)

          inTyCases :: Ty -> Ty -> Bool
          inTyCases rawtfunty rawargty =
            case ((rawRngTy funty argty),
                  (rawInTy funty nonFalseTy),
                  (rawInTy funty falseTy)) of
              (Just resty, Just posty, Just negty) ->
                -- if the argument is empty we don't have interesting
                -- info to compare, so just abort with success
                if (rawSubtype argty Impl.emptyTy)
                then True
                -- similarly, if the result is empty, just verify
                -- the argument type is not something that we would
                -- have predicted could be mapped to a false or non-false
                -- value (since it wasn't mapped to any value...)
                else if (rawSubtype resty Impl.emptyTy)
                then (not (rawSubtype argty (Impl.tyOr posty negty)))
                -- if the argument is something that
                -- we predict will be mapped to a non-false value,
                -- verify that indeed is the case
                else if (rawSubtype argty posty)
                then ((rawSubtype resty nonFalseTy)
                       && (not (rawSubtype resty falseTy))
                       && (not (rawSubtype argty negty)))
                -- if the argument is something that
                -- we predict will be mapped to false,
                -- verify that indeed is the case
                else if (rawSubtype argty negty)
                then ((rawSubtype resty falseTy)
                       && (not (rawSubtype resty nonFalseTy))
                       && (not (rawSubtype argty posty)))
                -- we can't tell if that argument type will be
                -- mapped to a false or non-false value, so
                -- go ahead and check that the predicted result
                -- type is non false or non-false
                else if (rawSubtype argty (Impl.tyOr posty negty))
                then ((not (rawSubtype resty falseTy))
                      && (not (rawSubtype resty nonFalseTy)))
                -- at this point, part of the argument type
                -- is not covered by the union of the predicted false
                -- and non-false type, which means that part is mapped
                -- to bottom, so verify if we isolate that part, the
                -- predicted function application result is empty
                else case coveredRng of
                       Nothing -> False
                       Just rng -> (rawSubtype rng Impl.emptyTy)
                where uncovered = (Impl.tyDiff argty (Impl.tyOr posty negty))
                      coveredRng = (rawRngTy funty uncovered)
              _ -> True
            where nonFalseTy = (parse (Not F))
                  falseTy = (parse F)
                  funty = (parse rawtfunty)
                  argty = (parse rawargty)
