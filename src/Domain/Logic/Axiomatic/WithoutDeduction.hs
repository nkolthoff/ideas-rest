module Domain.Logic.Axiomatic.WithoutDeduction where

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
import Domain.Logic.Axiomatic.ProofGenerator hiding (see, mmsee)

axiomaticNDExercise :: Exercise Env
axiomaticNDExercise = axiomaticExercise
   { exerciseId     = describe "Axiomatic proofs" $ 
                      newId "logic.propositional.axiomatic.nodeduction"
   , strategy       = axiomaticNoDeductionStrategy
   }

axiomaticNoDeductionStrategy :: LabeledStrategy (Context Env)
axiomaticNoDeductionStrategy = Library.label "axiomaticNoDeduction" $   
                                    axiomaticStrategy 
									.*. renumberProof
									.*. try (insertExtraMP .*. renumberProof)	
				          		--	.*. (removeDeduction .*. renumberProof)
				          		--	.*. (removeDeduction .*. renumberProof)
									.*. repeatS (removeDeduction .*. renumberProof .*. try (insertExtraMP .*. renumberProof))

see :: Int -> IO ()
see i = printDerivation axiomaticNDExercise (makeEnv $ exampleList !! i)

mmsee :: Int -> IO ()
mmsee i = printDerivation axiomaticNDExercise (makeEnv $ mmExampleList !! i)

-----------------------------------------------------------------------
-- verwijderen deductiestelling
removeDeduction :: Rule (Context Env)
removeDeduction = liftToContext $ makeRule "removeDeduction" trans
 where
  trans env@(Env _ _ p)   
       | filter isDeduction (prooflines p)/= [] && cond = Just env{goals = [] 
                                                          , availables = makeProof []
                                                          , proof = changedProof 
                                                                    <> duplass
                                                                    <> changeReferenceAA pf1 pf2refass changedProof
                                                                }
                                                          
        | filter isDeduction (prooflines p)/= []        = Just env{goals = [] 
                                                          , availables = makeProof []
                                                          , proof = changedProof
                                                                    <> changeReferenceAA pf1 pf2refded changedProof
                                                            }                                                   
       | otherwise = Nothing                
     where  isDeduction pl = fst (motivation pl)  == "Deduction"
            pf1 = fst $ splitbeforeDeduction p
            changedProof = moveDeduct  (fst $ splitbeforeDeduction p)(findDeduct p) (nextNumber p)
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
           
            
insertExtraMP :: Rule  (Context Env)         
insertExtraMP = liftToContext $ makeRule "insertExtraMP" trans
    where trans env@(Env _ _ p)   
                    | cond      = Just env { proof =  pf1 <> fst (duplicateMP pf1 pf2) <> snd (duplicateMP pf1 pf2)}  
                    | otherwise = Nothing 
                              where  
								  isDeduction pl = (fst (motivation pl)  == "Deduction")
								  lines          =  prooflines p
								  cond           = (filter isDeduction lines) /= [] 
								  pf1            = fst $ splitKeepDeduction p
								  pf2            = makeProof(snd $ splitKeepDeduction p)
  					
renumberProof :: Rule (Context Env)
renumberProof = liftToContext $ makeRule "renumberProof" trans
    where
       trans env@(Env _ _ p)   = Just env { proof = renumber p
                                          , availables = makeProof []}
      
     
findDeductions :: Proof Statement -> Proof Statement
findDeductions prf = makeProof $ f (prooflines prf)
  where f x = filter isDeduction  x
                  where  isDeduction pl = fst (motivation pl)  == "Deduction"

findFirstDeduction :: Proof Statement -> Proofline Statement
findFirstDeduction prf =  head $ filter isDeduction (prooflines prf)
                            where  isDeduction pl = fst (motivation pl)  == "Deduction"
                            
splitbeforeDeduction :: Proof Statement -> (Proof Statement, [Proofline Statement])
splitbeforeDeduction prf = (makeProof (fst res), rest)
               where res            = splitAt  n lines 
                     isDeduction pl = fst (motivation pl)  == "Deduction"
                     lines          =  (prooflines prf)
                     n              = head (references  $ findFirstDeduction prf)
                     rest           = (fst split)<> (tail (snd split)) 
                     split          = break  isDeduction  (snd res)
                     
splitKeepDeduction :: Proof Statement -> (Proof Statement, [Proofline Statement])
splitKeepDeduction prf = (makeProof (  fst split <> [head $ snd split]),  tail $ snd split)
               where              
                     isDeduction pl = fst (motivation pl)  == "Deduction"
                     lines          =  (prooflines prf)
                     split          = break  isDeduction  lines
                     
findIndexFirstDeduction:: [Proofline Statement] -> Int
findIndexFirstDeduction x  = fromJust (findIndex isDeduction x)
						where isDeduction pl = fst (motivation pl)  == "Deduction"
						
findIndexRefFirstDeduction:: [Proofline Statement] -> Int
findIndexRefFirstDeduction x  = fromJust (findIndex isDeduction x)
						where isDeduction pl = fst (motivation pl)  == "Deduction"
						
findDeduct :: Proof Statement -> SLogic
findDeduct x =  f (fromJust (term (findFirstDeduction x)))
    where f (as :|- (p :->: q)) = p
   
moveDeduct :: Proof Statement -> SLogic -> Int -> Proof Statement 
moveDeduct prf p n =  makeProof(f (prooflines prf) p n)
 where f [] p n = []
       f (x:xs) p n = (prooflines (fst(convertProofline prf x  p n))) <> (f xs p (snd(convertProofline prf x  p n)))
      
      
     

convertProofline :: Proof Statement -> Proofline Statement -> SLogic -> Int -> (Proof Statement, Int)
convertProofline prf pl  p nn
           | (label pl) == "Assumption" && p == q = (proofPimplP pl p nn, nn + 4)
           | axiomOrAss (label pl)                = (convertAxiom pl p q nn, nn + 2)
           | (label pl) == "Modus Ponens"         = (convertMP prf pl p  nn, nn + 2)  
           |otherwise                             = (prooflineNr n (as :|-  q) (label pl, references pl), nn)
           where
              as = assumptions $  fromJust (term pl)
              q = consequent $  fromJust (term pl)
              n = fromJust (number pl)
              axiomOrAss s = (s == "Axiom a")||(s == "Axiom b")||(s == "Axiom c")||(s == "Assumption")

                            
convertAxiom :: Proofline Statement -> SLogic  -> SLogic -> Int -> Proof Statement
convertAxiom pl p q nn =    (prooflineNr nn (fromJust (term pl)) (label pl, [])) 
                             <>(prooflineNr (nn + 1) (axiomA q p) ("Axiom a", []))
                             <> (prooflineNr (n) (as :|- (p :->: q)) ("Modus Ponens", [nn,nn + 1]))
                             
                       where
                            as = assumptions $  fromJust (term pl)
                            n  = fromJust (number pl)

proofPimplP :: Proofline Statement  -> SLogic -> Int -> Proof Statement
proofPimplP pl p nn =    (prooflineNr nn (axiomB  p (p :->: p) p) ("Axiom b", [])) 
                          <>(prooflineNr (nn + 1) (axiomA p (p :->: p)) ("Axiom a", []))
                          <> (prooflineNr (nn + 2) (S.empty :|- (p :->: (p:->:p)) :->:(p:->:p))("Modus Ponens", [nn,nn + 1]))
                          <>(prooflineNr (nn + 3) (axiomA p p) ("Axiom a", [])) 
                          <> (prooflineNr (n) (S.empty :|- (p:->:p))("Modus Ponens", [nn + 2,nn + 3]))
                       where
                            n  = fromJust (number pl) 
                           
convertMP :: Proof Statement -> Proofline Statement -> SLogic  ->  Int -> Proof Statement
convertMP prf pl p  nn  
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
                            cs1 = consequent pl1
                            cs2 = consequent pl2
                            isImpl (r :->: s) = True
                            isImpl x = False
                            prem (r :->: s) = r
                            prem x = x
                            cons  (r :->: s) = s
                            cons x = x
                            as3 = S.delete p (S.union as1 as2)
                            
changeReference :: Int -> Int -> Proof Statement -> Proof Statement
changeReference oud nieuw = rec . prooflines
 where 
   rec [] = mempty
   rec (pl:prf)  
      | elem oud (references pl) = 
          prooflineNr (fromMaybe 0 (number pl)) (fromJust (term pl)) (fst $ motivation pl, delete oud (nieuw:(references pl)) )
           <> rec prf
      | otherwise = makeProof [pl] <> rec prf
      
findReference :: Int -> Proof Statement -> Bool
findReference oud = rec . prooflines
 where 
   rec []        = False
   rec (pl:prf)  = elem oud (references pl)|| rec prf 
 
      
duplicateMP :: Proof Statement -> Proof Statement -> (Proof Statement, Proof Statement)
duplicateMP pf1 pf2  
                   = rec listMP pf2
           --     | listMP  /= []  = (renumberFrom  n (stripProof t pf1), pfnew)
           --     | otherwise      = (makeProof [], pf2)
                where 
                    list   = findReferences pf1 pf2
         --           t1      =  fromJust (term $ fromJust( findNumber (head listMP) pf1))
                    t  nn    =  fromJust (term $ fromJust( findNumber (nn) pf1))
                    listMP =  [n | n <- list 
                                 ,(label $fromJust( findNumber n pf1)) == "Modus Ponens" ]              
                    n      =  (maximum $ usedNumbers pf2) + 1 
                    max n t1 = maximum $ usedNumbers (renumberFrom  n (stripProof t1 pf1))
              --     pfnew = changeReference (head listMP) m pf2
                    rec []  p2 = (makeProof [], p2)
                    rec (x:xs) p2 = ((renumberFrom  ((maximum $ usedNumbers (fst (rec xs p2) <> (snd (rec xs p2)))) + 1)  (stripProof (t x) pf1))<> fst (rec xs p2), changeReference x  (max n (t x)) p2)


findReferences :: Proof Statement -> Proof Statement -> [Int]
findReferences pf1 pf2 = nub (rec  (prooflines pf2))
 where 
   rec [] = []
   rec (pl:prf) = filter (< (nextNumber pf1 -1 ) ) (references pl) <> rec prf
   
-- omdat eerst verwijzingen naar p |- p via duplass gedupliceerd zijn, hoeft hier niet meer op gecontroleerd te worden   
changeReferenceAA :: Proof Statement ->Proof Statement  -> Proof Statement ->  Proof Statement  
changeReferenceAA  pf1 pf2 changedpf =  foldl referenceNew pf2 listAA
                where
                  list   = findReferences pf1 pf2
                  listAA =  [n | n <- list 
                               ,(axiomOrAss $ label $fromJust(findNumber n pf1))]   
                  axiomOrAss s = (s == "Axiom a")||(s == "Axiom b")||(s == "Axiom c")||(s == "Assumption")
                  referenceNew pf n = changeReference n (f n) pf
                  f n | (cond n) = n
                  f n | otherwise = head $ references (fromJust(findNumber n changedpf)) 
                  cond n = axiomOrAss $ label $fromJust(findNumber n changedpf)