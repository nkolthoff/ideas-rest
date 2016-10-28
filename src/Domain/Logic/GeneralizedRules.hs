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
--  $Id: GeneralizedRules.hs 8757 2015-10-21 10:39:16Z bastiaan $

module Domain.Logic.GeneralizedRules
   ( generalRuleDeMorganOr, generalRuleDeMorganAnd
   , generalRuleDistrAnd, generalRuleDistrOr
   ) where

-- Note: the generalized rules do not take AC-unification into account,
-- and perhaps they should.
import Control.Monad
import Data.Function
import Data.List
import Domain.Logic.Formula
import Domain.Logic.Utils
import Ideas.Common.Library

-----------------------------------------------------------------------------
-- Generalized rules

generalRuleDeMorganOr :: Rule SLogic
generalRuleDeMorganOr =
   siblingOf groupDeMorgan $ makeListRule "GenDeMorganOr" f
 where
   f (Not e) = do
      xs <- subDisjunctions e
      guard (length xs > 2)
      return (ands (map Not xs))
   f _ = []

generalRuleDeMorganAnd :: Rule SLogic
generalRuleDeMorganAnd =
   siblingOf groupDeMorgan $ makeListRule "GenDeMorganAnd" f
 where
   f (Not e) = do
      xs <- subConjunctions e
      guard (length xs > 2)
      return (ors (map Not xs))
   f _ = []

generalRuleDistrAnd :: Rule SLogic
generalRuleDistrAnd =
   siblingOf groupDistribution $ makeListRule "GenAndOverOr" f
 where
   f p = do -- left distributive
      (leftCtx, x, y, rightCtx) <- getConjunctionTop p 
      ys <- subDisjunctions y
      guard (length ys > 2)
      return (ands (leftCtx ++ [ors (map (x :&&:) ys)] ++ rightCtx))
    `mplus` do -- right distributive
      (leftCtx, x, y, rightCtx) <- getConjunctionTop p 
      xs <- subDisjunctions x
      guard (length xs > 2)
      return (ands (leftCtx ++ [ors (map (:&&: y) xs)] ++ rightCtx))

generalRuleDistrOr :: Rule SLogic
generalRuleDistrOr =
   siblingOf groupDistribution $ makeListRule "GenOrOverAnd" f
 where
   f p = do -- left distributive
      (leftCtx, x, y, rightCtx) <- getDisjunctionTop p
      ys <- subConjunctions y
      guard (length ys > 2)
      return (ors (leftCtx ++ [ands (map (x :||:) ys)] ++ rightCtx))
    `mplus` do -- right distributive
       (leftCtx, x, y, rightCtx) <- getDisjunctionTop p
       xs <- subConjunctions x
       guard (length xs > 2)
       return (ors (leftCtx ++ [ands (map (:||: y) xs)] ++ rightCtx))

-------------------------------------------------------------------------
-- Helper functions

getDisjunctionTop :: SLogic -> [([SLogic], SLogic, SLogic, [SLogic])]
getDisjunctionTop = map f . split4 . disjunctions
 where
   f (x, y, z, u) = (x, ors y, ors z, u)

getConjunctionTop :: SLogic -> [([SLogic], SLogic, SLogic, [SLogic])]
getConjunctionTop = map f . split4 . conjunctions
 where
   f (x, y, z, u) = (x, ands y, ands z, u)
   
split4 :: [a] -> [([a], [a], [a], [a])]
split4 as = sortBy (compare `on` smallContext)
   [ (xs1, xs2, ys1, ys2) 
   | (xs, ys) <- split as
   , (xs1, xs2) <- split xs
   , not (null xs2)
   , (ys1, ys2) <- split ys
   , not (null ys1)
   ]
 where
   -- This order tries to use as many elements as possible as distribuant
   -- (small/empty left and right contexts are preferable)
   smallContext (xs, _, _, ys) = length xs + length ys

split :: [a] -> [([a], [a])]
split xs = map (`splitAt` xs) [0 .. length xs]  

-- All combinations where some disjunctions are grouped, and others are not
subDisjunctions :: SLogic -> [[SLogic]]
subDisjunctions = subformulas (:||:) . disjunctions

subConjunctions :: SLogic -> [[SLogic]]
subConjunctions = subformulas (:&&:) . conjunctions

subformulas :: (a -> a -> a) -> [a] -> [[a]]
subformulas _  []     = []
subformulas _  [x]    = [[x]]
subformulas op (x:xs) = map (x:) yss ++ [ op x y : ys| y:ys <- yss ]
 where
   yss = subformulas op xs