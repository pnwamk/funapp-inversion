module Types.MetafunctionsSpec (spec) where


import Test.Hspec
import Types.Syntax
import qualified Types.LazyBDD as BDD
import qualified Types.Subtype as S
import qualified Types.Metafunctions as M
import Types.MetafunctionTests
import Types.NumericTower

  
spec :: Spec
spec = (genMetafunctionSpec
         (BDD.parseTy baseEnv)
         (S.subtype baseEnv)
         (S.overlap baseEnv)
         (S.equiv baseEnv)
         (M.fstProj baseEnv)
         (M.sndProj baseEnv)
         (M.domTy baseEnv)
         (M.rngTy baseEnv)
         (M.inTy baseEnv))
