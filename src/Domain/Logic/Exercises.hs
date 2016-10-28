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
-- Exercise for the logic domain, used for the OUNL course
-- "Discrete Wiskunde A (DWA)"
--
-----------------------------------------------------------------------------
--  $Id: Exercises.hs 7527 2015-04-08 07:58:06Z bastiaan $

module Domain.Logic.Exercises
   ( dnfExercise, dnfUnicodeExercise, cnfExercise, cnfUnicodeExercise
   , extraLogicRules
   ) where

import Data.Maybe
import Domain.Logic.BuggyRules
import Domain.Logic.Examples
import Domain.Logic.Formula
import Domain.Logic.GeneralizedRules
import Domain.Logic.Generator
import Domain.Logic.InverseRules
import Domain.Logic.Parser
import Domain.Logic.Rules
import Domain.Logic.Strategies
import Domain.Logic.Utils
import Ideas.Common.Library
import Test.QuickCheck

-- Currently, we use the DWA strategy
dnfExercise :: Exercise SLogic
dnfExercise = makeExercise
   { exerciseId     = describe "Proposition to DNF" $
                         propositionalId # "dnf"
   , status         = Stable
   , parser         = parseLogicPars
   , prettyPrinter  = ppLogicPars
   , equivalence    = withoutContext eqLogic
   , similarity     = withoutContext equalLogicA
   , ready          = predicate isDNF
   , suitable       = predicate notTooManyEquivs
   , extraRules     = map liftToContext (extraLogicRules ++ buggyRules)
   , strategy       = dnfStrategy
   , navigation     = navigator
   , testGenerator  = Just (arbitrary `suchThat` notTooManyEquivs)
   , randomExercise = useGenerator dnfExerciseGenerator
   , examples       = dnfExamples
   }

-- Direct support for unicode characters
dnfUnicodeExercise :: Exercise SLogic
dnfUnicodeExercise = dnfExercise
   { exerciseId    = describe "Proposition to DNF (unicode support)" $
                        propositionalId # "dnf.unicode"
   , parser        = parseLogicUnicodePars
   , prettyPrinter = ppLogicUnicodePars
   }

cnfExercise :: Exercise SLogic
cnfExercise = makeExercise
   { exerciseId     = describe "Proposition to CNF" $
                         propositionalId # "cnf"
   , status         = Stable
   , parser         = parseLogicPars
   , prettyPrinter  = ppLogicPars
   , equivalence    = withoutContext eqLogic
   , similarity     = withoutContext equalLogicA
   , ready          = predicate isCNF
   , suitable       = predicate notTooManyEquivs
   , extraRules     = map liftToContext (extraLogicRules ++ buggyRules)
   , strategy       = cnfStrategy
   , navigation     = navigator
   , testGenerator  = Just (arbitrary `suchThat` notTooManyEquivs)
   , randomExercise = useGenerator cnfExerciseGenerator
   , examples       = cnfExamples
   }

cnfUnicodeExercise :: Exercise SLogic
cnfUnicodeExercise = cnfExercise
   { exerciseId     = describe "Proposition to CNF (unicode support)" $
                         propositionalId # "cnf.unicode"
   , parser         = parseLogicUnicodePars
   , prettyPrinter  = ppLogicUnicodePars
   }

extraLogicRules :: [Rule SLogic]
extraLogicRules =
   [ ruleCommOr, ruleCommAnd, ruleAssocOr, ruleAssocAnd
   , generalRuleDistrOr, ruleDistrOr
   , generalRuleDistrAnd, ruleDistrAnd
   , inverseDeMorganOr, inverseDeMorganAnd
   , inverseAndOverOr, inverseOrOverAnd
   ] ++ inverseRules

notTooManyEquivs :: SLogic -> Bool
notTooManyEquivs = (<=2) . countEquivalences

dnfExerciseGenerator :: Maybe Difficulty -> Gen SLogic
dnfExerciseGenerator = exerciseGeneratorFor dnfExercise

cnfExerciseGenerator :: Maybe Difficulty -> Gen SLogic
cnfExerciseGenerator = exerciseGeneratorFor cnfUnicodeExercise

exerciseGeneratorFor :: Exercise SLogic -> Maybe Difficulty -> Gen SLogic
exerciseGeneratorFor ex mdif =
   let (gen, (minStep, maxStep)) = generateLevel (fromMaybe Medium mdif)
       ok p = let i = fromMaybe maxBound (stepsRemaining maxStep p)
              in notTooManyEquivs p && i >= minStep && i <= maxStep
   in gen `suchThat` ok
 where
   stepsRemaining i =
      checkLength i ex

checkLength :: Int -> Exercise a -> a -> Maybe Int
checkLength n ex a = defaultDerivation ex a >>= rec 0 . steps
 where
   rec i []       = Just i
   rec i (_:xs)
      | i >= n    = Nothing
      | otherwise = rec (i+1) xs

-- QuickCheck property to monitor the number of steps needed
-- to normalize a random proposition (30-40% is ok)
{-
testGen :: Property
testGen = forAll generateLogic $ \p ->
   let n = steps p
   in countEquivalences p <= 2 ==> label (show (n >= 4 && n <= 12)) True

testme :: IO ()
testme = quickCheck testGen

start = ((r :<->: p) :||: (q :->: s)) :&&: (Not s :<->: (p :||: r))
 where
  (p, q, r, s) = (Var "p", Var "q", Var "r", Var "s")

go = derivation . emptyState dnfExercise
-}