-----------------------------------------------------------------------------
-- Copyright 2015, Open Universiteit Nederland. This file is distributed
-- under the terms of the GNU General Public License. For more information,
-- see the file "LICENSE.txt", which is included in the distribution.
-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan.heeren@ou.nl
-- Stability   :  provisional
-- Portability :  portable (depends on ghc)
--
-- Generalized rules, and inverse rules, for De Morgan and distributivity
--
-----------------------------------------------------------------------------
--  $Id: InverseRules.hs 7527 2015-04-08 07:58:06Z bastiaan $

module Domain.Logic.InverseRules
   ( inverseDeMorganOr, inverseDeMorganAnd
   , inverseAndOverOr, inverseOrOverAnd
   , inverseRules
   ) where

-- Note: the generalized rules do not take AC-unification into account,
-- and perhaps they should.
import Control.Monad
import Domain.Logic.Formula
-- import Domain.Logic.Generator
import Domain.Logic.Utils
-- import Domain.Logic.Rules
import Ideas.Common.Library

-----------------------------------------------------------------------------
-- Inverse rules

-- generalized (works for multiple terms)
inverseDeMorganOr :: Rule SLogic
inverseDeMorganOr = siblingOf groupDeMorgan $
   makeSimpleRule "InvDeMorganOr" $ \p -> do
      let xs = conjunctions p
      guard (length xs > 1)
      ys <- mapM isComplement xs
      return (Not $ ors ys)

-- generalized (works for multiple terms)
inverseDeMorganAnd :: Rule SLogic
inverseDeMorganAnd = siblingOf groupDeMorgan $
   makeSimpleRule "InvDeMorganAnd" $ \p -> do
      let xs = disjunctions p
      guard (length xs > 1)
      ys <- mapM isComplement xs
      return (Not $ ands ys)

inverseAndOverOr :: Rule SLogic
inverseAndOverOr = siblingOf groupDistribution $
   makeSimpleRule "InvAndOverOr" $ \p -> do
      let xs = disjunctions p
      guard (length xs > 1)
      do pairs <- mapM isAndHead xs
         let (as, ys) = unzip pairs
         guard (allSame as)
         return (head as :&&: ors ys)
       `mplus` do
         pairs <- mapM isAndLast xs
         let (ys, as) = unzip pairs
         guard (allSame as)
         return (ors ys :&&: head as)

inverseOrOverAnd :: Rule SLogic
inverseOrOverAnd = siblingOf groupDistribution $
   makeSimpleRule "InvOrOverAnd" $ \p -> do
      let xs = conjunctions p
      guard (length xs > 1)
      do pairs <- mapM isOrHead xs
         let (as, ys) = unzip pairs
         guard (allSame as)
         return (head as :||: ands ys)
       `mplus` do
         pairs <- mapM isOrLast xs
         let (ys, as) = unzip pairs
         guard (allSame as)
         return (ands ys :||: head as)

isAndHead, isAndLast, isOrHead, isOrLast :: SLogic -> Maybe (SLogic, SLogic)
isAndHead = useHead (:&&:) . conjunctions
isAndLast = useLast (:&&:) . conjunctions
isOrHead  = useHead (:||:) . disjunctions
isOrLast  = useLast (:||:) . disjunctions

useHead, useLast :: (a -> a -> a) -> [a] -> Maybe (a, a)
useHead op (x:xs) | not (null xs) =
   Just (x, foldr1 op xs)
useHead _ _ = Nothing

useLast op = fmap (\(x, y) -> (y, x)) . useHead (flip op) . reverse

allSame :: Eq a => [a] -> Bool
allSame []     = True
allSame (x:xs) = all (==x) xs

-----------------------------------------------------------------------------
-- More inverse rules

inverseRules :: [Rule SLogic]
inverseRules =
   [ invDefImpl, invDefEquiv, invDoubleNeg, invIdempOr, invIdempAnd
   , invTrueAnd, invNotTrue, invFalseOr, invNotFalse
   , invDistrAnd, invDistrOr
   -- , invAbsorpOr, invAbsorpAnd, invTrueOr, invComplOr, invFalseAnd
   -- , invComplAnd, invDistrAnd, invDistrOr
   ]

invDefImpl :: Rule SLogic
invDefImpl = siblingOf groupImplication $ rewriteRule "DefImpl.inv" $
   \x y -> Not x :||: y  :~>  x :->: y

invDefEquiv :: Rule SLogic
invDefEquiv = siblingOf groupEquivalence $ rewriteRule "DefEquiv.inv" $
   \x y -> (x :&&: y) :||: (Not x :&&: Not y)  :~>  x :<->: y

invDoubleNeg :: Rule SLogic
invDoubleNeg = siblingOf groupDoubleNegation $ rewriteRule "NotNot.inv" $
   \x -> x  :~>  Not (Not x)

invIdempOr :: Rule SLogic
invIdempOr = siblingOf groupIdempotency $ rewriteRule "IdempOr.inv" $
   \x -> x  :~>  x :||: x

invIdempAnd :: Rule SLogic
invIdempAnd = siblingOf groupIdempotency $ rewriteRule "IdempAnd.inv" $
   \x -> x :~> x :&&: x

invTrueAnd :: Rule SLogic
invTrueAnd = siblingOf groupTrueConjunction $ rewriteRules "TrueZeroAnd.inv"
   [ \x -> x  :~>  T :&&: x
   , \x -> x  :~>  x :&&: T
   ]

invNotTrue :: Rule SLogic
invNotTrue = siblingOf groupNotTrue $ rewriteRule "NotTrue.inv" $
   F  :~>  Not T

invFalseOr :: Rule SLogic
invFalseOr = siblingOf groupFalseDisjunction $ rewriteRules "FalseZeroOr.inv"
   [ \x -> x  :~>  F :||: x
   , \x -> x  :~>  x :||: F
   ]

invNotFalse :: Rule SLogic
invNotFalse = siblingOf groupNotFalse $ rewriteRule "NotFalse.inv" $
   T  :~> Not F

invDistrAnd :: Rule SLogic
invDistrAnd = siblingOf groupDistribution $ rewriteRules "AndOverOr.inv"
   [ \x y z -> (x :&&: y) :||: (x :&&: z)  :~>  x :&&: (y :||: z)
   , \x y z -> (x :&&: z) :||: (y :&&: z)  :~>  (x :||: y) :&&: z
   ]

invDistrOr :: Rule SLogic
invDistrOr = siblingOf groupDistribution $ rewriteRules "OrOverAnd.inv"
   [ \x y z -> (x :||: y) :&&: (x :||: z)  :~>  x :||: (y :&&: z)
   , \x y z -> (x :||: z) :&&: (y :||: z)  :~>  (x :&&: y) :||: z
   ]

{- TO DO: fix code below
proofInvRule :: String -> Rule SLogic -> Rule SLogic
proofInvRule = makeInvRule equalLogicA

invAbsorpOr, invAbsorpAnd, invTrueOr, invComplOr, invFalseAnd,
   invComplAnd, invDistrAnd, invDistrOr :: Rule SLogic
invAbsorpOr  = proofInvRule "AbsorpOr.inv" ruleAbsorpOr
invAbsorpAnd = proofInvRule "AbsorpAnd.inv" ruleAbsorpAnd
invTrueOr    = proofInvRule "TrueZeroOr.inv" ruleTrueOr
invComplOr   = proofInvRule "ComplOr.inv" ruleComplOr
invFalseAnd  = proofInvRule "FalseZeroAnd.inv" ruleFalseAnd
invComplAnd  = proofInvRule "ComplAnd.inv" ruleComplAnd
invDistrAnd  = proofInvRule "AndOverOr.inv" ruleDistrAnd -- see GeneralizedRules
invDistrOr   = proofInvRule "OrOverAnd.inv" ruleDistrOr  -- see GeneralizedRules
-}