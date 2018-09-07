module Types.NMetafunctionsSpec (spec) where


import Test.Hspec
import Types.Syntax
import qualified Types.LazyBDD as BDD
import qualified Types.Subtype as S
import qualified Types.NMetafunctions as M
import Types.MetafunctionTests
import Types.BaseEnv
  
spec :: Spec
spec = (genMetafunctionSpec
         (BDD.parseTy baseEnv)
         S.subtype
         S.overlap
         S.equiv
         M.fstProj
         M.sndProj
         M.domTy
         M.rngTy
         M.inTy)
