module Domain.Logic.Axiomatic.BuggyRules (buggyRules) where

import Data.Maybe
import Ideas.Common.Library
import Domain.Logic.Axiomatic.Statement
import Domain.Logic.LinearProof
import Domain.Logic.Axiomatic.Rules
import Domain.Logic.Formula

buggyRules :: [Rule (Proof Statement)]
buggyRules = [bugMP]

-- Buggy rules

bugMP :: Rule (Proof Statement)
bugMP = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw1") $ mustHaveParameters f (0, 0)
 where
   f = parameter2 "n1" "n2" $ \x y ->
      makeTrans (\p -> if mpForwardBug x y p then Just p else Nothing)

mpForwardBug :: Int -> Int -> Proof Statement -> Bool
mpForwardBug n1 n2 prf = fromMaybe False $ do
   st1 <- findNumber n1 prf >>= term
   st2 <- findNumber n2 prf >>= term
   return (fits (consequent st1) (consequent st2))
 where
   fits (p :->: q) r | q == r && p /= q = True
   fits p (q :->: r) | p == r && q /= r = True
   fits _ _ = False
