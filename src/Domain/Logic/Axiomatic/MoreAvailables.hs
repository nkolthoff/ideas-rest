module Domain.Logic.Axiomatic.MoreAvailables where

import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S
import Ideas.Utils.Prelude (ShowString(..))
import Ideas.Common.Library hiding (label)
import qualified Ideas.Common.Library as Library
import Domain.Logic.Formula
import Domain.Logic.Parser
import Domain.Logic.LinearProof hiding (addAssumption)
import Domain.Logic.Axiomatic.Statement
import Domain.Logic.Axiomatic.Examples
import Domain.Logic.Axiomatic.ProofGenerator hiding (see)
import Domain.Logic.Axiomatic.Optimised hiding (see)
import Domain.Logic.Axiomatic.WithoutDeduction hiding (see)
import Domain.Logic.ProofDAG

axiomaticATExercise :: Exercise Env
axiomaticATExercise = axiomaticExercise
   { exerciseId     = describe "Axiomatic proofs" $ 
                      newId "logic.propositional.axiomatic.smartnodeduction"
   , strategy       = axiomaticAvailableTreeStrategy
   }

{-
axiomaticDAGExercise :: Exercise (Proof Statement)
axiomaticDAGExercise = emptyExercise
   { prettyPrinter = show
   , strategy = Library.label "" $ liftToContext $ strategyGenerator axiomaticTranslator $ makeDag goal (availables env)
   }
 where
   env = fromJust $ fromContext $ fromJust $ 
         apply axiomaticAvailableTreeStrategy (inContext axiomaticATExercise (makeEnv (mmExampleList !! 1))) 
   goal = fromJust $ term $ last $ prooflines $ proof env -}

axiomaticAVStrategy :: LabeledStrategy (Context Env)
axiomaticAVStrategy = Library.label "axiomatic-availables" $
   (untilS stop 
      $  goalAvailable
      |> implicationIntroStep
      |> implicationIntro
      |> elimGoalStep
      |> elimGoal
  --    |> axiomBheuristic1 .*. repeatS (modusPonens)
  --    |> axiomBheuristic2 
      |> axiomCheuristic1 .*. repeatS (modusPonens)
  --    |> axiomCheuristic3 .*. repeatS (modusPonens)
  --    |> axiomCheuristic2 .*. repeatS (modusPonens)
      |> modusPonens
      |> doubleNegation
      |> deduction
      |> falseAsGoal
      |> negAsGoal 
      |> skipFalse
      |> contradiction1S
      |> contradiction1a .*. deduction .*. repeatS (implicationIntroStep) .*. contradiction1S
      |> contradiction2S
      |> contradiction3 
      |> contradiction4
      |> contradiction5
      |> contradiction6 .*. repeatS (modusPonens) |> deduction |> implicationIntroStep 
      |> contradiction7
      |> contradiction
      |> useImplAssumption)
      .*. repeatS deleteUnusedLines
 where
   stop = maybe True (null . goals) . fromContext

axiomaticAvailableTreeStrategy :: LabeledStrategy (Context Env)
axiomaticAvailableTreeStrategy = Library.label "axiomaticAvailableTree" $   
                                    axiomaticAVStrategy
                                    .*. repeatS removeDuplicateAv
 
                                    .*. try axiomABAvailable
                                    .*. try modusPonensTree
                                    .*. try modusPonensTree
                                    .*. try axiomCAvailable
                                    .*. try modusPonensTree
                                    .*. try axiomACAvailable
                                    .*. try modusPonensTree
                                    .*. try modusPonensTree 
                                    .*. try axiomAAvailable
                                    .*. try modusPonensTree
                                    .*. try axiomBAvailable1 
                                    .*. try modusPonensTree
                                    .*. try modusPonensTree
                                    .*. repeatS modusPonens

see :: Int -> IO ()
see i = printDerivation axiomaticATExercise (makeEnv $ mmExampleList !! i)

--dagsee :: Int -> IO ()
--dagsee i = printDerivation axiomaticDAGExercise mempty
-----------------------------------------------------------------------------------------
---breder maken van availables

axiomBAvailable1 :: Rule (Context Env)
axiomBAvailable1 = liftToContext $ makeRule "axiomBAvailable1" trans
 where
    trans env | null doubleImpList       = Nothing
              | otherwise                = Just env {availables = availables env <> new}
       where
          new = mconcat (zipWith ($) fs [nextNumber (availables env) ..])
          fs  = [ \i -> prooflineNr i (axB st) ("Axiom b", [])
                | st  <- doubleImpList]
          doubleImp (p :->: (q :->: r)) = True
          doubleImp x = False
          axB (p :->: (q :->: r)) = axiomB p q  r
          doubleImpList     = nub (filter (doubleImp) (concat[ S.elems (assumptions st)
												        	| pl <- prooflines (proof env)
													        , st <- maybeToList (term pl)]))    
													        
--variant op lege toepassing van deductiestelling													        
axiomAAvailable :: Rule (Context Env)
axiomAAvailable = liftToContext $ makeRule "axiomAAvailable" trans
 where
   trans env
      | null fs   = Nothing
      | otherwise = Just env { availables = availables env <> new }
    where
      new = mconcat (zipWith ($) fs [nextNumber (availables env) ..])
      sts  = nub [st 
                 |  pl1 <- prooflines (availables env)
                 , pl2 <- prooflines (availables env)
                 , st <- (axA (term pl1) (term pl2))
                 , findInProof  st  (availables env) == Nothing
                 ]   
      fs  = [ \i -> prooflineNr i st ("Axiom a", [])
            | st  <- sts
            ]    
     
      axA (Just (as1 :|- p :->: q1)) (Just (as2 :|- q2)) | ((q1 == q2) && (p `S.notMember` as2)) =  [ axiomA q1 p ] 
      axA _ _                                                                                             = []            
   
    
axiomABAvailable :: Rule (Context Env)
axiomABAvailable = liftToContext $ makeRule "axiomAB-available" trans
 where
   trans env
      | null fs   = Nothing
      | otherwise = Just env { availables = availables env <> new }
    where
      new = mconcat (zipWith ($) fs [nextNumber (availables env) ..])
      fs  = [ \i -> prooflineNr i ast ("Axiom a", [])
            | pl1 <- assList
            , st <-  prlList
            , let con = consequent st
            , ast  <- axAB pl1 con
            ]
                       
      axAB ( p1 :->: (q1 :->: r)) q2 | q1 == q2 = [axiomA q1 p1]
      axAB _ _                                  = []
      prlList                                  = nub [ st
					                                 | pl <- prooflines (proof env)
					                                 , st <- maybeToList (term pl)]
      assList                                  = nub (concat[ S.elems (assumptions st)
						                                    | pl <- prooflines (proof env)
						                                    , st <- maybeToList (term pl)])

								
axiomCAvailable :: Rule (Context Env)
axiomCAvailable = liftToContext $ makeRule "axiomAvailable" trans
 where
    trans env 
     | null fs     = Nothing
     | otherwise   = Just env {availables = availables env <> new}
        where
          new = mconcat (zipWith ($) fs [nextNumber (availables env) ..])
          fs  = [ \i -> prooflineNr i (axC st) ("Axiom c", [])
                | st  <- negImpList
                , findInProof (axC st)  (availables env) == Nothing]
          negImp (Not p :->: Not q) = True
          negImp x = False
          axC (Not p :->: Not q) = axiomC p q 
          negImpList     = nub (filter (negImp) (concat[ S.elems (assumptions st)
												        	| pl <- prooflines (proof env)
													        , st <- maybeToList (term pl)]))    

    
axiomACAvailable :: Rule (Context Env)
axiomACAvailable = liftToContext $ makeRule "axiomAC-available" trans
 where
   trans env
      | null fs   = Nothing
      | otherwise = Just env { availables = availables env <> new }
    where
      new = mconcat (zipWith ($) (fs ++ gs) [nextNumber (availables env) ..])
      fs  = [ \i -> prooflineNr i ast ("Axiom c", [])
            | pl1 <- assList
            , st <-  prlList
            , let con = consequent st
            , ast  <- axC pl1 con
            , findInProof ast  (availables env) == Nothing
            ]
      gs  = [ \i -> prooflineNr i ast ("Axiom a", [])
            | pl1 <- assList
            , st <-  prlList
            , let con = consequent st
            , ast  <- axA pl1 con
            , findInProof ast  (availables env) == Nothing
            ]                 
      axC  (Not p1)  (p2 :->: q) | p1 == p2 = [axiomC q p1]
      axC _ _                                  = []
      axA  (Not p1)  (p2 :->: q) | p1 == p2 = [axiomA (Not q)(Not p1)]
      axA _ _                                  = []
      assList     = nub  (concat[ S.elems (assumptions st)
						        | pl <- prooflines (proof env)
								, st <- maybeToList (term pl)])
      prlList     = nub   [ st
						  | pl <- prooflines (proof env)
						  , st <- maybeToList (term pl)]
   
{-    
transitiveAxiomB:: Rule (Context Env)
transitiveAxiomB = liftToContext $ makeRule "transitiveAxiomB" trans
 where
   trans env							
-}								
								
-- is nu misschien te streng, omdat andere routes naar een eerdere toepassing van deductie zo niet gevonden worden.
modusPonensTree :: Rule (Context Env)
modusPonensTree = liftToContext $ makeRule "modus-ponens-tree" trans
 where
   trans env
      | null fs   = Nothing
      | otherwise = Just env { availables = availables env <> new }
    where
      new = mconcat (zipWith ($) fs [nextNumber (availables env) ..])
      fs  = [ \i -> prooflineNr i st ("Modus Ponens", maybeToList (number pl1) ++ maybeToList (number pl2))
            | pl1 <- prooflines (availables env)
            , pl2 <- prooflines (availables env)
            , st  <- applyMP (term pl1) (term pl2)
            , all ( (\t -> not (equalMP t  st [(fromJust $ number pl1)  ,(fromJust $ number pl2)]))) (prooflines (availables env))
            , not (isGoal pl1 || isGoal pl2)
            , not (isDeduction pl1 pl2)
            , not (conclusionIsAss (term pl1) (term pl2))
            , restrictAssumptions pl1 pl2
            ]
                       
      applyMP (Just (as1 :|- p1 :->: q)) (Just (as2 :|- p2)) | p1 == p2 =
         [ as1 `S.union` as2 :|- q ] 
      applyMP _ _ = []
      isMP x = (label  x ) == "Modus Ponens"
      equalMP t1 t2 [n1, n2]= isMP t1 && (references t1 \\ [n1, n2] == [])
      isGoal st = term st == ( term $ last  $ prooflines (proof env))
      isDeduction pl1 pl2 = (label pl1 == "Deduction") || (label pl2 == "Deduction")
      conclusionIsAss (Just (as1 :|- p1 :->: q)) (Just (as2 :|- p2)) | p1 == p2 =  q `S.member` (as1 `S.union` as2) 
      conclusionIsAss (Just (as1 :|- p1 )) (Just (as2 :|- p2 :->: q))| p1 == p2 =  q `S.member` (as1 `S.union` as2) 
      conclusionIsAss _ _   =  False  
      restrictAssumptions  pl1 pl2 =  ((assumptions  $ fromJust $ term pl1) `S.union` (assumptions $ fromJust $ term  pl2)) `S.isSubsetOf ` ( assumptions (fromJust $ term  $ last  $ prooflines (proof env)))
                   
                   
removeDuplicateAv:: Rule (Context Env)
removeDuplicateAv = liftToContext $ makeRule "removeDuplicateAv" trans
   where 
     trans env@(Env _ avail _ )   |(findDuplicate avail /= Nothing) = Just env{availables = newproof avail}                              
                               | otherwise   = Nothing
     hulp avail = makeProof $ delete  (snd $ fromJust $ (findDuplicate avail)) (prooflines avail)
     newproof avail  = changeReference  (oud avail) (nieuw avail) (hulp avail)
     oud avail = fromJust $ number (snd $ fromJust $ (findDuplicate avail))
     nieuw avail = fromJust $ number (fst $ fromJust $ (findDuplicate avail))
