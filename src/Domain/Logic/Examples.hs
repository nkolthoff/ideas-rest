-----------------------------------------------------------------------------
-- Copyright 2015, Open Universiteit Nederland. This file is distributed
-- under the terms of the GNU General Public License. For more information,
-- see the file "LICENSE.txt", which is included in the distribution.
-----------------------------------------------------------------------------
-- |
-- Maintainer  :  josje.lodder@ou.nl
-- Stability   :  provisional
-- Portability :  portable (depends on ghc)
--
-- A set of example proofs
--
-----------------------------------------------------------------------------
--  $Id: Examples.hs 7527 2015-04-08 07:58:06Z bastiaan $

module Domain.Logic.Examples
   ( dnfExamples, cnfExamples, exampleProofs
   ) where

import Domain.Logic.Formula
import Ideas.Common.Exercise
import Ideas.Utils.Prelude (ShowString(..))

dnfExamples :: Examples SLogic
dnfExamples =
   [ (Easy, Not(q :->: r) :||: q :||: r)
   , (Medium, (Not q :&&: Not (p :->: q)) :->: p)
   , (Medium, ((q :||: Not r) :&&: (q :||: p) :&&: Not q))
   , (Medium, Not p :<->: (p :&&: q))
   , (Difficult, (p :||: q) :&&: (r :<->: p))
   ]
   -- ((q :&&: r) :->: (q :->: r)) :->: (r :&&: (q :->: p))
   -- (q :&&: p) :<->: (q :&&: r)
   -- Not ((p :&&: q) :<->: (Not r :||: q))
 where
   p = Var (ShowString "p")
   q = Var (ShowString "q")
   r = Var (ShowString "r")

cnfExamples :: Examples SLogic
cnfExamples =
   [ (Easy, Not ((q :->: r) :->: Not q))
   , (Easy, (Not q :&&: Not (p :->: q)) :->: p)
   , (Medium, ((q :||: p) :->: (q :->: p)) :->: (r :&&: q :&&: p))
   , (Medium, p :<->: (p :&&: q))
   , (Difficult, (p :&&: q) :||: (p :<->: r))
   ]
   -- Not (q :->: r) :||: q :||: r
   -- ((q :||: p) :&&: (p :||: r)) :||: Not (q :||: r)
   -- (q :&&: p) :<->: (q :&&: r)
 where
   p = Var (ShowString "p")
   q = Var (ShowString "q")
   r = Var (ShowString "r")

exampleProofs :: Examples (SLogic, SLogic)
exampleProofs =
   [ {- 16 -} easy      (Not(p :&&: q) :||: (s :||: Not r), (p :&&: q) :->: (r :->: s))
   , {- 13 -} medium    (Not((p :->:q) :->: (p:&&:q)), (p :->: q) :&&: (Not p :||: Not q))
   , {- 14 -} medium    (Not((p :<->: q) :->: (p :||: (p :<->: q))), F)
   , {-  3 -} difficult ((p :&&: Not q):||:(q :&&: Not p), (p :||:q):&&:Not(p :&&: q))
   , {- 28 -} difficult ((p :&&: (q :&&: r)) :||: (Not p :&&: q), (Not p :&&: (q :&&: Not r)) :||: ( q :&&: r))

   , {-  4 -} easy      (Not(p :||: Not(p :||: Not q)), Not(p :||: q))
   , {-  6 -} medium    ((p :&&: q) :->: p, T)
   , {- 12 -} medium    ((p :->: q):->: (p :->: s), (Not q :->: Not p) :->: (Not s :->: Not p))
   , {- 19 -} easy      (p :&&: q, Not(p :->: Not q))
   , {-  1 -} medium    (Not(p :||: (Not p :&&: q)), Not(p :||: q))
   , {-  2 -} medium    ((p :->: q):||: Not p, (p :->: q) :||: q)
   , {-  5 -} difficult (p :<->: q, (p :->: q) :&&: (q :->: p))
   , {-  7 -} medium    ((p :->: q) :||: (q :->: p), T)
   , {-  8 -} difficult ((q :->: (Not p :->: q)) :->: p, Not p :->: (q :&&: ((p :&&: q) :&&: q)))
   , {-  9 -} medium    ((p :->: Not q):->:q, (s :||:(s :->:(q :||: p))) :&&: q)
   , {- 10 -} difficult (p :->: (q :->: r), (p :->: q) :->: (p :->:r))
   , {- 11 -} difficult (Not((p :->: q) :->: Not(q :->: p)), p :<->: q)
   , {- 15 -} easy      (q :&&: p, p :&&: (q :||: q))
   , {- 17 -} easy      (Not(Not p :&&: Not(q :||: r)),  p :||: (q :||: r))
   , {- 18 -} easy      (Not (p :&&: (q :||: r)), Not p :||: (Not q :&&: Not r))
   , {- 20 -} difficult (p :<->: (q :<->: p),q)
   , {- 21 -} medium    ((p :->: q) :->: Not p, p :->: (q :->: Not p))
   , {- 22 -} medium    ((Not q :&&: p) :->: p, (Not q :<->: q) :->: p)
   , {- 23 -} easy      (p :<->: q, Not p :<->: Not q)
   , {- 24 -} difficult ((p :->: q) :<->: (p :->: r), (p :->: (q :&&: r)) :||: Not(p :->: (q :||: r)))
   , {- 25 -} medium    (p :<->: (p :&&: q), p :->: q)
   , {- 26 -} medium    (p :<->: (p :->: q), p :&&: q)
   , {- 27 -} medium    ((p :->: q ) :&&: (r :->: q), (p :||: r) :->: q)
   , {- 29 -} difficult (p :||: (q :&&: r), ( p :&&: Not q) :||: ( p :&&: Not r):||: ( q :&&: r))
   , {- 30 -} difficult ((p :&&: q) :||: (Not q :&&: r), ( p :&&: r) :||: ( p :&&: q :&&: Not r):||: (Not p :&&: Not q :&&: r))
   , {- 31 -} medium    (p :&&: (q :||: s), (q :&&: Not s :&&: p) :||: (p :&&: s))
   ]
 where
   easy      x = (Easy, x)
   medium    x = (Medium, x)
   difficult x = (Difficult, x)

   p = Var (ShowString "p")
   q = Var (ShowString "q")
   s = Var (ShowString "s")
   r = Var (ShowString "r")

{-
makeTestCases :: IO ()
makeTestCases = zipWithM_ makeTestCase [0..] exampleProofs

makeTestCase :: Int -> (SLogic, SLogic) -> IO ()
makeTestCase n (p, q) =
   writeFile ("proof" ++ show n ++ ".json")
      (json $ show p ++ " == " ++ show q)

json :: String -> String
json s = unlines
   [ "{ \"method\" : \"derivation\""
   , ", \"params\" : [[\"logic.proof\", \"[]\", " ++ show s ++ ", \"\"]]"
   , ", \"id\"     : 42"
   , "}"
   ] -}