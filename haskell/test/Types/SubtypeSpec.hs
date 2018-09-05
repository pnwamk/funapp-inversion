module Types.SubtypeSpec (spec) where


import Test.Hspec
import qualified Types.Subtype as S
import qualified Types.LazyBDD as BDD
import Types.Syntax
import Types.SubtypeTests
import Types.NumericTower

spec :: Spec
spec = (genSubtypeSpec
        (BDD.parseTy baseEnv)
        S.subtype
        S.overlap
        S.equiv)
