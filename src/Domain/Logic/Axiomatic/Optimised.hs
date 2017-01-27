module Domain.Logic.Axiomatic.Optimised where

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
import Domain.Logic.Axiomatic.ProofGenerator hiding (see, mmsee)
import Domain.Logic.Axiomatic.Statement
import Domain.Logic.Axiomatic.Examples
import Domain.Logic.Axiomatic.WithoutDeduction hiding (see, mmsee)

axiomaticSDExercise :: Exercise Env
axiomaticSDExercise = axiomaticExercise
   { exerciseId     = describe "Axiomatic proofs" $ 
                      newId "logic.propositional.axiomatic.smartnodeduction"
   , strategy       = axiomaticSmartNDStrategy
   } 
   
axiomaticSmartNDStrategy :: LabeledStrategy (Context Env)
axiomaticSmartNDStrategy = Library.label "axiomaticSmartNoDeduction" $   
                                    axiomaticStrategy
                                    .*. minimizeAssumptions
									.*. renumberProof
									.*. try (insertExtraMP .*. renumberProof)
									.*. repeatS (smartRemoveDeduction .*. renumberProof .*. try (insertExtraMP .*. renumberProof))
                                    .*. repeatS (deleteUnusedLines |> removeDuplicate )
                                    .*. renumberProof

see :: Int -> IO ()
see i = printDerivation axiomaticSDExercise (makeEnv $ exampleList !! i)

mmsee :: Int -> IO ()
mmsee i = printDerivation axiomaticSDExercise (makeEnv $ mmExampleList !! i)
               
----------------------------------------------------------------------------------------------------------------------------
-- optimalisaties van verwijderen deductiestelling
smartRemoveDeduction :: Rule (Context Env)
smartRemoveDeduction = liftToContext $ makeRule "smartRemoveDeduction" trans
 where
  trans env@(Env _ _ p)   
       | filter isDeduction (prooflines p)/= [] && cond2 = Just env{goals = [] 
                                                          , availables = makeProof []
                                                          , proof =  pfk1 
                                                                    <> newline
                                                                    <> dedline
                                                                    <> pfk2
                                                        
                                                                 
                                                                       
                                                          }
       | filter isDeduction (prooflines p)/= [] && cond = Just env{goals = [] 
                                                          , availables = makeProof []
                                                          , proof = 
                                                                   repairMP changedProof (findDeduct p)
                                                                    <> duplass
                                                                    <> changeReferenceAA pf1 pf2refass changedProof
                                                                    
 
                                                                       
                                                          }
                                                          
        | filter isDeduction (prooflines p)/= []        = Just env{goals = [] 
                                                          , availables = makeProof []
                                                          , proof =
                                                                     repairMP changedProof (findDeduct p)
                                                                     <> changeReferenceAA pf1 pf2refded changedProof
                                                           
  
                                                          }                                                   
       | otherwise = Nothing                
     where  isDeduction pl = fst (motivation pl)  == "Deduction"
            pf1 = fst $ splitbeforeDeduction p
            changedProof = smartMoveDeduct  (fst $ splitbeforeDeduction p) p (findDeduct p) (nextNumber p)
            nn = (maximum $ usedNumbers changedProof) + 1
            oud = (findIndexFirstDeduction $ prooflines p) + 1
            nieuw = head (references  $ findFirstDeduction p)
            dedass = ((S.singleton $ findDeduct p) :|- findDeduct p)
            pl1  | isNothing (findInProofBy (subStatement dedass) p) = []
                 | otherwise                                         =  [fromJust(findInProofBy (subStatement dedass) p)]
            duplass = prooflineNr nn  dedass ("Assumption", [])  
            cond | pl1 == [] = False
                 | otherwise = findReference (fromJust (number $ head pl1))  $ makeProof (snd $ splitbeforeDeduction p)
            pf2refded = (changeReference oud nieuw (makeProof (snd $ splitbeforeDeduction p)))
            pf2refass = changeReference (fromJust (number $ head pl1)) nn pf2refded
            n         = length $ prooflines changedProof
            cond2     = (findDeduct p) `S.notMember` (assumptions $ fromJust (term (fromJust (findNumber nieuw p))))
            newline  = prooflineNr (nextNumber p)(axiomA cons (findDeduct p)) ("Axiom a", [])
            ass = assumptions $ fromJust (term (fromJust (findNumber nieuw p)))
            cons = consequent $ fromJust (term (fromJust (findNumber nieuw p)))
            pfk1 = makeProof $ init ( prooflines (fst $ splitKeepDeduction p))
            deduction = last ( prooflines (fst $ splitKeepDeduction p))
            dedline = prooflineNr (fromJust (number deduction)) (fromJust(term deduction)) ("Modus Ponens", [head (references deduction),nextNumber p])
            pfk2 = makeProof (snd $ splitKeepDeduction p)
            
repairMP :: Proof Statement -> SLogic -> Proof Statement
repairMP prf p = makeProof ( f (prooflines  prf) p )
     where 
			   f [] p  = []
			   f (x:xs) p | isIncorrectMP x = (prooflines (changeRef (oud x) (nieuw x) x))<> f xs p
			   f (x:xs) p | otherwise = x : (f xs p)
			   isIncorrectMP x = ((label  x ) == "Modus Ponens") && incorrect x
			   isMP x = (label  x ) == "Modus Ponens"
			   changeRef oud nieuw x = prooflineNr (fromJust (number x))  (fromJust( term x)) ("Modus Ponens", nieuw : (delete oud (references x))) 
		--	   oud x = 24
			   nieuw x =fromJust( number $ line x)
			   incorrect x = not (((isImpl $ cs1 x) && ((prem  $ cs1 x)  == (cs2 x ))) ||((isImpl $ cs2 x) && ((prem  $ cs2 x) == (cs1 x))))
			   mp1 x = fromJust(findNumber (head(references x)) prf)
			   mp2 x = fromJust(findNumber (last(references x)) prf)
			   pl1 x = fromJust (term  $ mp1 x)
			   pl2 x = fromJust (term  $ mp2 x)
			   as1 x =  S.delete p (assumptions $ pl1 x)
			   as2 x =  S.delete p (assumptions $ pl2 x )
			   cs1 x = consequent $ pl1 x
			   cs2 x = consequent $ pl2 x
			   isImpl (r :->: s) = True
			   isImpl x = False
			   prem (r :->: s) = r
			   prem x = x
			   oud x | ((isImpl $ cs1 x) && ((prem  $ cs1 x)  == (p :->: cs2 x )))= fromJust(number $ mp2 x)
			   oud x | otherwise = fromJust (number $ mp1 x)
			   line x = head  ([p |p <- (prooflines prf)
			                       ,isMP p
			                       , elem (oud x) (references p)])


		   
smartMoveDeduct :: Proof Statement -> Proof Statement -> SLogic -> Int -> Proof Statement 
smartMoveDeduct prf wholepf p n =  makeProof(f ( prooflines prf) p n)
 where f [] p n = []
       f (x:xs) p n = (prooflines (fst(smartConvertProofline prf wholepf x  p n))) <> (f xs p (snd(smartConvertProofline prf wholepf x  p n)))
       
smartConvertProofline :: Proof Statement -> Proof Statement -> Proofline Statement -> SLogic -> Int -> (Proof Statement, Int)
smartConvertProofline prf wholepf pl  p nn
           | isUsed && not (cond)      					  = (insertImpl pl p nn, nn + 2) 
		   | cond && (label pl)  == "Assumption" && p == q = (proofPimplP pl p nn, nn + 4)
           | cond && axiomOrAss (label pl)                = (convertAxiom pl p q nn, nn + 2)
           | cond && (label pl) == "Modus Ponens"         = (smartConvertMP prf pl p  nn, nn + 2)  
           |otherwise                             = (prooflineNr n (as :|-  q) (label pl, references pl), nn)
           where
              as = S.union (assumptions $  fromJust (term pl)) (assumptions $  fromJust (term pl)) 
              q = consequent $  fromJust (term pl)
              n = fromJust (number pl)
              axiomOrAss s = (s == "Axiom a")||(s == "Axiom b")||(s == "Axiom c")||(s == "Assumption")
              cond = (p  `S.member` as)
              isUsed = any ( == n)(concat $  map references   lines)
              lines = filter usedMP (prooflines wholepf)
              usedMP pl = label pl == "Modus Ponens" && p  `S.member` (assumptions $  fromJust (term pl))
              
insertImpl :: Proofline Statement  -> SLogic -> Int ->  Proof Statement
insertImpl pl p nn =    makeProof [pl] 
                          <>(prooflineNr (nn ) (axiomA q p) ("Axiom a", []))      
                          <> (prooflineNr (nn + 1) (as :|- (p:->:q ))("Modus Ponens", [n,nn]))
                       where
                            n  = maybe (-1) (\x -> x) (number pl) 
                            -- kan ik hier een loze consequent invoeren?
                            q =  maybe q consequent (term pl)
                            as = maybe S.empty assumptions (term pl)
                            
--eigenlijk nog niet smart, want dit deel kan geschrapt
smartConvertMP :: Proof Statement -> Proofline Statement -> SLogic  ->  Int -> Proof Statement
smartConvertMP prf pl p  nn  
{-
               | isImpl cs1 && cs2 == p && (S.member p ass1)   = (prooflineNr nn (axiomA (p :->: (cons cs1)) (p :->: p)  ) ("Axiom a", []))
                                                                 <> (prooflineNr (nn + 1) (as1 :|- ((p :->: p) :->: (p :->: (cons cs1)))) ("Modus Ponens", [fromJust (number mp1), nn])) 
                                                                 <> (prooflineNr n (as1 :|-  (p :->: (cons cs1))) ("Modus Ponens", [fromJust (number mp2), nn + 1]))
               | isImpl cs2 && cs1 == p && (S.member p ass2)   = (prooflineNr nn (axiomA (p :->: (cons cs2)) (p :->: p)  ) ("Axiom a", []))
                                                                 <> (prooflineNr (nn + 1) (as1 :|- ((p :->: p) :->: (p :->: (cons cs2)))) ("Modus Ponens", [fromJust (number mp2), nn])) 
                                                                 <> (prooflineNr n (as1 :|-  (p :->: (cons cs2))) ("Modus Ponens", [fromJust (number mp1), nn + 1]))                             
-} 
               | isImpl cs1 && (prem cs1 == cs2) = (prooflineNr nn (axiomB  p (cs2) (cons cs1)) ("Axiom b", [])) 
                                                      <> (prooflineNr (nn + 1) (as1 :|- ((p :->: cs2) :->: (p :->: (cons cs1)))) ("Modus Ponens", [fromJust (number mp1), nn])) 
                                                      <> (prooflineNr n (as3 :|-  (p :->: (cons cs1))) ("Modus Ponens", [fromJust (number mp2), nn + 1])) 
               | otherwise = (prooflineNr nn (axiomB  p (cs1) (cons cs2)) ("Axiom b", [])) 
                                                      <> (prooflineNr (nn + 1) (as2 :|- ((p :->: cs1) :->: (p :->: (cons cs2)))) ("Modus Ponens", [fromJust (number mp2), nn])) 
                                                      <> (prooflineNr n (as3 :|-  (p :->: (cons cs2))) ("Modus Ponens", [fromJust (number mp1), nn + 1]))    
                       where
                            as = assumptions $  fromJust (term pl)
                            n  = fromJust (number pl) 
                            mp1 = fromJust(findNumber (head(references pl)) prf)
                            mp2 = fromJust(findNumber (last (references pl))prf)
                            pl1 = fromJust (term mp1)
                            pl2 = fromJust (term mp2)
                            as1 =  S.delete p (assumptions pl1)
                            as2 =  S.delete p (assumptions pl2)
                            ass1 =  S.delete p (assumptions pl1)
                            ass2 =  S.delete p (assumptions pl2)
                            cs1 = consequent pl1
                            cs2 = consequent pl2
                            isImpl (r :->: s) = True
                            isImpl x = False
                            prem (r :->: s) = r
                            prem x = x
                            cons  (r :->: s) = s
                            cons x = x
                            as3 = S.delete p (S.union as1 as2)
   
findDuplicate :: Proof Statement -> (Maybe (Proofline Statement, Proofline Statement))
findDuplicate prf | [(x, y)| x <- prooflines prf
                                , y <- prooflines prf
                                , subStatement (fromJust $ term  x) (fromJust $ term y)
                                , (fromJust $ number x) < (fromJust  $ number y)
                          ]   /= []                                          = Just $ head [(x, y)| x <- prooflines prf
                                													, y <- prooflines prf
                                													, subStatement (fromJust $ term  x) (fromJust $ term y)
                                													, (fromJust $ number x) < (fromJust $ number y)]
                   | otherwise                                               = Nothing             													    			  

												    			  
                   
                   
                   
removeDuplicate:: Rule (Context Env)
removeDuplicate = liftToContext $ makeRule "removeDuplicate" trans
   where 
     trans env@(Env _ _ prf)   |(findDuplicate prf /= Nothing) = Just env{proof = newproof prf}                              
                               | otherwise   = Nothing
     hulp prf = makeProof $ delete  (snd $ fromJust $ (findDuplicate prf)) (prooflines prf)
     newproof prf | duplicateIsGoal prf = makeProof  $ (takeWhile (/= (fst $ fromJust $ (findDuplicate prf))) (prooflines prf)) ++ [fst $ fromJust $ (findDuplicate prf)]
                  | otherwise = changeReference  (oud prf) (nieuw prf) (hulp prf)
     oud prf = fromJust $ number (snd $ fromJust $ (findDuplicate prf))
     nieuw prf = fromJust $ number (fst $ fromJust $ (findDuplicate prf))
     duplicateIsGoal prf = (fromJust $ number (snd $ fromJust $ (findDuplicate prf))) == (maximum (usedNumbers prf)) 

     
minimizeAssumptions :: Rule (Context Env) 
minimizeAssumptions = liftToContext $ makeRule "minimizeAssumptions" trans
    where 
         trans env@(Env _ _ prf)    = Just env{proof = newproof prf} 
         newproof prf = mconcat $ map (minAss prf) (prooflines prf)
         minAss prf x  | isAssumption x = makeProof [newAssumptions x (S.singleton (consequent $ fromJust $ term x))]  
         minAss prf x  | isModusPonens x = makeProof [newAssumptions x (asmp x prf)] 
         minAss prf x | otherwise = makeProof [x]
         isAssumption x = label x == "Assumption"
         isModusPonens x = (label x == "Modus Ponens")
         asmp x prf = S.union (as1 x prf) (as2 x prf)
         as1 x prf = assumptions $ st1 x prf 
         as2 x prf = assumptions $ st2 x prf 
         st1 x prf = fromJust (term $ fromJust (findNumber (head (references x)) prf))
         st2 x prf = fromJust (term $ fromJust (findNumber (last (references x)) prf))
         
newAssumptions :: Proofline Statement -> S.Set SLogic ->  (Proofline Statement)
newAssumptions  pl as  =   pl { term = Just (as :|- (consequent  (fromJust $  term pl) ))}