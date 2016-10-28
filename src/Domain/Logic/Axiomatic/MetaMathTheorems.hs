{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Domain.Logic.Axiomatic.MetaMathTheorems where

import Control.Monad
import Data.List hiding (insert)
import Data.Maybe
import Data.Monoid
import Domain.Logic.Formula
import Domain.Logic.Parser
import Domain.Logic.LinearProof
import Domain.Logic.Axiomatic.Optimised  hiding (removeDuplicate)
import Domain.Logic.Axiomatic.WithoutDeduction
import Domain.Logic.Axiomatic.Statement
import Domain.Logic.Axiomatic.Examples
import Ideas.Common.Library hiding (label)
import Ideas.Common.Utils (ShowString(..))
--import Ideas.Encoding.Encoder
import qualified Data.Set as S
--import Ideas.Text.JSON

instance Read SLogic where
   readsPrec _ s =
      case parseLogicPars s of
         Left _  -> []
         Right p -> [(p, "")]


assumption :: SLogic -> Proof Statement -> Proof Statement
assumption phi = forward ([phi] |- phi) (unqualified assumptionId, [])

introAxiomA :: SLogic -> SLogic -> Proof Statement -> Proof Statement
introAxiomA phi psi = forward (axiomA phi psi) (unqualified axiomAId, [])

introAxiomB :: SLogic -> SLogic -> SLogic -> Proof Statement -> Proof Statement
introAxiomB phi psi chi = forward (axiomB phi psi chi) (unqualified axiomBId, [])

introAxiomC :: SLogic -> SLogic -> Proof Statement -> Proof Statement
introAxiomC phi psi = forward (axiomC phi psi) (unqualified axiomCId, [])

assumptionId :: Id
assumptionId = describe "Introduces an assumption (phi)." $ 
   newId "logic.propositional.axiomatic.assumption"

axiomAId, axiomBId, axiomCId :: Id
axiomAId = describe "Introduces an instance of Axiom A (phi, psi)." $ 
   newId "logic.propositional.axiomatic.axiom-a"
axiomBId = describe "Introduces an instance of Axiom B (phi, psi, chi)." $ 
   newId "logic.propositional.axiomatic.axiom-b"
axiomCId = describe "Introduces an instance of Axiom C (phi, psi)." $ 
   newId "logic.propositional.axiomatic.axiom-c"   

mpForwardId :: Id
mpForwardId = describe "Modus ponens applied to phi and phi -> psi." $ 
   newId "logic.propositional.axiomatic.modusponens.forward"

modusPonensForward :: Int -> Int -> Proof Statement -> Maybe (Proof Statement)
modusPonensForward n1 n2 prf = do
   st1 <- findNumber n1 prf >>= term
   st2 <- findNumber n2 prf >>= term
   psi <- fits (consequent st1) (consequent st2)
   let st  = assumptions st1 `S.union` assumptions st2 :|- psi
       mot = ("Modus Ponens", [n1, n2])
   return (forward st mot prf)
 where
   fits (p :->: q) r | p == r = Just q
   fits p (q :->: r) | p == q = Just r
   fits _ _ = Nothing

   
forward :: Statement -> Motivation -> Proof Statement -> Proof Statement
forward st m prf = insert pl prf
 where
   n  = nextNumber prf
   pl = prooflineNr n st m

insert :: Proof a -> Proof a -> Proof a
insert prf1 prf2 = makeProof (xs ++ prooflines prf1 ++ ys)
 where
   n = maximum (0 : usedNumbers prf1)
   (xs, ys) = break (maybe False (> n) . number) (prooflines prf2)
   
   
removeDuplicate:: Proof Statement -> Proof Statement
removeDuplicate prf  = rec prf 
   where 
     rec prf  |(findDuplicate prf == Nothing) = prf                              
              | otherwise   = rec (newproof prf)
        where                        
              hulp prf = makeProof $ delete  (snd $ fromJust $ (findDuplicate prf)) (prooflines prf)
              newproof prf | duplicateIsGoal prf = makeProof  $ (takeWhile (/= (fst $ fromJust $ (findDuplicate prf))) (prooflines prf)) ++ [fst $ fromJust $ (findDuplicate prf)]
                  | otherwise = changeReference  (oud prf) (nieuw prf) (hulp prf)
              oud prf = fromJust $ number (snd $ fromJust $ (findDuplicate prf))
              nieuw prf = fromJust $ number (fst $ fromJust $ (findDuplicate prf))
              duplicateIsGoal prf = (fromJust $ number (snd $ fromJust $ (findDuplicate prf))) == (maximum (usedNumbers prf)) 
              
deleteUnusedLines :: Proof Statement -> Proof Statement
deleteUnusedLines prf = rec prf
  where
    rec prf   |not (unUsedlines prf) = prf                             
              | otherwise   = rec (newproof prf)
    newproof prf  = makeProof  $ (filter (isUsed prf)(init $ prooflines prf)) ++ [last $ prooflines prf] 
    isUsed  prf x =  any (== fromJust (number x) )(concat $  map references (prooflines prf))
    isNotUsed prf x = not( any ( == fromJust (number x))(concat $  map references (prooflines prf)))
    unUsedlines prf = any  (isNotUsed prf) (init $ prooflines prf)
   
-------------------------------------
-- Metamath-theorems

a1i :: Int -> SLogic ->  Proof Statement -> Maybe (Proof Statement)
a1i n1 psi prf = do
   st <- findNumber n1 prf >>= term
   let phi = consequent st
   return  (fromJust (modusPonensForward n1 n2 (introAxiomA phi psi prf)))
 where
      n2  = nextNumber prf
      
mp1i :: Int -> Int -> SLogic ->  Proof Statement -> Maybe (Proof Statement)
mp1i n1 n2 chi prf = do
   return $ fromJust (a1i n3 chi (fromJust (modusPonensForward n1 n2 prf)))
 where
      n3  = nextNumber prf      

a2i :: Int ->  Proof Statement -> Maybe (Proof Statement)      
a2i n1 prf = do
   st <- findNumber n1 prf >>= term
   let phi = consequent st
   return   (fromJust $ modusPonensForward n1 n2 (introAxiomB (p1 phi)(p2 phi)(p3 phi) prf))
 where
      n2  = nextNumber prf
      p1 (p :->: (q :->: r))    =  p
      p2 (p :->: (q :->: r))    =  q
      p3 (p :->: (q :->: r))    =  r

imim2i :: Int ->  SLogic ->  Proof Statement -> Maybe (Proof Statement)
imim2i n1  chi prf = do
   return $ fromJust (a2i n2 (fromJust (a1i n1 chi prf)))
 where
      n2  = nextNumber prf       
      
mpd :: Int ->  Int ->  Proof Statement -> Maybe (Proof Statement)
mpd n1 n2 prf = do
   return $ fromJust (modusPonensForward n1 n3 (fromJust (a2i n2 prf)))
 where
      newprf  = fromJust (a2i n2 prf)          
      n3      = (nextNumber newprf)  - 1
      
syl :: Int ->  Int ->  Proof Statement -> Maybe (Proof Statement)
syl n1 n2 prf = do
   st <- findNumber n1 prf >>= term
   let phi =  p1 (consequent st)
       newprf  = fromJust (a1i n2 phi prf)  
       n3      = (nextNumber newprf)  - 1 
   return $ fromJust (mpd n1 n3 (fromJust (a1i n2 phi prf)))
 where
      p1 (p :->: q)    =  p         
 
mpi :: Int ->  Int ->  Proof Statement -> Maybe (Proof Statement)
mpi n1 n2 prf = do
   st <- findNumber n2 prf >>= term
   let phi =  p1 (consequent st)
       newprf  = fromJust (a1i n1 phi prf)  
       n3      = (nextNumber newprf) - 1   
   return $ fromJust (mpd n3 n2 newprf)
 where
   p1 (p :->: (q :->: r))    =  p   

--invoegen met merge!--   
id1 :: SLogic  -> Proof Statement -> Maybe (Proof Statement) 
id1 phi  prf  = do 
       let  p1  = prooflineNr 1 (axiomA phi phi) ( "Axiom a", [])
            p2  = prooflineNr 2 (axiomA phi (phi :->: phi) ) ( "Axiom a", [])
            p3  = prooflineNr 3 (axiomB phi (phi :->: phi) phi ) ( "Axiom b", []) 
            newprf = p1 <> p2 <> p3
       return  $ renumber $ merge  prf (fromJust (modusPonensForward 1 4 (fromJust $ modusPonensForward 2 3 newprf))) 

   
a1d :: Int ->  SLogic ->  Proof Statement -> Maybe (Proof Statement)
a1d n  chi prf = do  
     st <- findNumber n prf >>= term
     let psi =  pr (consequent st)  
         pl  = prooflineNr n1 (axiomA psi chi) ( "Axiom a", [])
         newprf  =  prf <> pl
         n1      = (nextNumber prf) 
     return $ fromJust (syl n n1 newprf)
 where
   pr (q :->: r)    =  r  
   
a2d :: Int ->   Proof Statement -> Maybe (Proof Statement)
a2d n1  prf = do  
     st <- findNumber n1 prf >>= term
     let psi =  p2 (consequent st)
         chi =  p3 (consequent st)
         the =  p4 (consequent st)
         pl  = prooflineNr n2 (axiomB psi chi the) ( "Axiom b", [])
         newprf  =  prf <> pl
         n2      = (nextNumber prf) 
     return $ fromJust (syl n1 n2 newprf)
 where
      p2 (p :->: (q :->: (r :->: s))) =  q
      p3 (p :->: (q :->: (r :->: s))) =  r 
      p4 (p :->: (q :->: (r :->: s))) =  s
      
sylcom :: Int -> Int -> Proof Statement -> Maybe (Proof Statement)      
sylcom n1 n2 prf = do
   let newprf  = fromJust (a2i n2 prf)
       n3  = nextNumber newprf - 1
   return   (fromJust $ syl n1 n3 newprf)
   
   

syl5com :: Int -> Int -> Proof Statement -> Maybe (Proof Statement)      
syl5com n1 n2 prf = do
     st <- findNumber n2 prf >>= term
     let psi =  p1 (consequent st)   
         newprf  = fromJust (a1d n1 psi prf)
         n3  = nextNumber newprf - 1
     return   (fromJust $ sylcom n3 n2 newprf)
 where
      p1 (p :->: (q :->: r))    =  p

com12 :: Int -> Proof Statement -> Maybe (Proof Statement) 
com12 n1 prf = do
      st <- findNumber n1 prf >>= term
      let psi =  p2 (consequent st)
          newprf  = fromJust (id1 psi prf)
          n2  = nextNumber newprf - 1   
      return $ renumber $ deleteUnusedLines (removeDuplicate(fromJust $ syl5com n2 n1 newprf) )   
  where
      p2 (p :->: (q :->: r))    =  q

syl5 :: Int -> Int -> Proof Statement -> Maybe (Proof Statement)      
syl5 n1 n2 prf = do
     let newprf  = fromJust (syl5com n1 n2 prf)
         n3  = nextNumber newprf - 1
     return   (fromJust $ com12 n3  newprf)


      
syl6 :: Int -> Int -> Proof Statement -> Maybe (Proof Statement)      
syl6 n1 n2 prf = do
     st <- findNumber n1 prf >>= term
     let psi =  p2 (consequent st)   
         newprf  = fromJust (a1i n2 psi prf)
         n3  = nextNumber newprf - 1
     return   (fromJust $ sylcom n1 n3 newprf)
 where
      p2 (p :->: (q :->: r))    =  q
      
pm227 ::  SLogic -> SLogic -> Proof Statement -> Maybe (Proof Statement)      
pm227 phi psi prf = do
     let newprf = fromJust $ id1 (phi :->: psi) prf   
         n  = nextNumber newprf - 1   
     return (fromJust $ com12 n newprf) 
     
      
mpdd  :: Int -> Int -> Proof Statement -> Maybe (Proof Statement)      
mpdd n1 n2 prf = do   
     let newprf = fromJust $ a2d n2 prf
         n3 = nextNumber newprf - 1
     return $ fromJust (mpd n1 n3 newprf)
     
mpid  :: Int -> Int -> Proof Statement -> Maybe (Proof Statement)      
mpid n1 n2 prf = do   
     st <- findNumber n2 prf >>= term
     let psi =  p2 (consequent st)      
         newprf = fromJust $ a1d n1 psi prf
         n3 = nextNumber newprf - 1
     return $ fromJust (mpdd n3 n2 newprf)
 where
      p2 (p :->: (q :->: r))    =  q
      
pm243i ::  Int -> Proof Statement -> Maybe (Proof Statement)     
pm243i n1 prf = do   
     st <- findNumber n1 prf >>= term
     let phi =  p1 (consequent st)
         newprf = renumber $ fromJust (id1 phi prf)        
     return $ fromJust (mpd (nextNumber newprf - 1) n1 newprf)
 where
      p1 (p :->: q)    =  p
      n2 = nextNumber prf
      
pm243a ::  Int -> Proof Statement -> Maybe (Proof Statement)     
pm243a n1 prf = do   
     st <- findNumber n1 prf >>= term
     let psi =  p1 (consequent st)
         newprf = renumber $ fromJust (id1 psi prf)        
     return $ renumber $ deleteUnusedLines (removeDuplicate (fromJust (mpid (nextNumber newprf - 1) n1 newprf)))
 where
      p1 (p :->: q)    =  p

pm243 ::  SLogic -> SLogic -> Proof Statement -> Maybe (Proof Statement)      
pm243 phi psi prf = do
     let newprf = fromJust $ pm227 phi psi prf   
         n  = nextNumber newprf - 1   
     return (fromJust $ a2i n newprf) 
     
imim2d  ::  Int -> SLogic -> Proof Statement -> Maybe (Proof Statement)      
imim2d n1 psi prf = do
     let newprf = fromJust $ a1d n1 psi prf   
         n2  = nextNumber newprf - 1   
     return (fromJust $ a2d n2 newprf) 
         
imim2  ::  SLogic -> SLogic -> SLogic -> Proof Statement -> Maybe (Proof Statement)      
imim2 phi psi chi prf = do
     let newprf = fromJust $ id1 (phi :->: psi) prf   
         n2  = nextNumber newprf - 1   
     return $ renumber $ deleteUnusedLines (removeDuplicate(fromJust $ imim2d n2  chi newprf))
     
     
imim12i ::  Int -> Int -> Proof Statement -> Maybe (Proof Statement)      
imim12i n1 n2 prf = do   
     st <- findNumber n1 prf >>= term
     let psi =  p2 (consequent st) 
         newprf = fromJust $ imim2i n1 psi prf
         n3 = nextNumber newprf - 1
     return $ fromJust (syl5 n1 n3 newprf)
 where   
      p2 (p :->: q)    =  q
      
main :: IO ()   
main = print exProof

exProof :: Proof Statement
exProof = fromJust (make mempty)
 where
   make =  -- return.assumption (p :->: (q :->: (p :->: r)))
   --       return . assumption  p
        return . assumption (p :->: q)
    >=> return . assumption (r :->: (q :->: s))
    --    >=> return.assumption (p :->: (q :->: (r :->: s)))
     --  return.assumption ((p :->: q) :->: (p :->: q))
    --      >=> return . assumption (r :->: s)
 --     >=> return . assumption (q :->: (r :->: s))
    >=>  syl5  1 2 

 --     >=> modusPonensForward 2 1
 --   >=> return . assumption (p :->: q)
   p = Var (ShowString "p")
   q = Var (ShowString "q")
   r = Var (ShowString "r")
   s = Var (ShowString "s")
   
   -- follows from deduction
axiomA :: SLogic -> SLogic -> Statement
axiomA phi psi = S.empty :|- phi :->: (psi :->: phi)

-- follows from deduction
axiomB :: SLogic -> SLogic -> SLogic -> Statement
axiomB phi psi chi = S.empty :|- (phi :->: (psi :->: chi)) :->: ((phi :->: psi) :->: (phi :->: chi))

axiomC :: SLogic -> SLogic -> Statement
axiomC phi psi = S.empty :|- (Not phi :->: Not psi) :->: (psi :->: phi)