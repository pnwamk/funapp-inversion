module Types.LazyBDDSpec ( spec ) where

import Test.Hspec
import Test.QuickCheck
--import qualified Types.Syntax as Stx
import Types.LazyBDD
import Types.NumericTower
import Types.Subtype
import qualified Repl.Parse as Parse


spec :: Spec
spec = do
  describe "parse/readBack type tests" $ do
    it "inverse" $ property $
      (\rawT -> (let t = parseTy baseEnv rawT in
                  case (Parse.parseTy baseEnv (readBackTy t)) of
                    Left _ -> False
                    Right (t', _) -> equiv t t'))
