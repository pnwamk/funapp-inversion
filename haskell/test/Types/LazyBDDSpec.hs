module Types.LazyBDDSpec ( spec ) where

import Test.Hspec
import Test.QuickCheck
--import qualified Types.Syntax as Stx
import Types.LazyBDD
import Types.Subtype
import Repl.Parser


spec :: Spec
spec = do
  describe "parse/readBack type tests" $ do
    it "inverse" $ property $
      (\rawT -> let t = parseTy rawT in
                  case (strToTy (readBackTy t)) of
                    Nothing -> False
                    Just t' -> equiv t t')
