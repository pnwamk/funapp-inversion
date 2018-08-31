module Types.NSubtypeSpec (spec) where


import Test.Hspec
import Test.QuickCheck
import qualified Types.NSubtype as N
import qualified Types.LazyBDD as BDD
import Types.Syntax
import Types.SubtypeTests
import Types.NumericTower

spec :: Spec
spec = (genSubtypeSpec
        (BDD.parseTy baseEnv)
        (N.subtype baseEnv)
        (N.overlap baseEnv)
        (N.equiv baseEnv))
