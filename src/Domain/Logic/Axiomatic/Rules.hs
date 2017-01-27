{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Domain.Logic.Axiomatic.Rules 
   ( assumptionId, axiomAId, axiomBId, axiomCId, mpId, dedId
   -- rules 
   , assumptionR, assumptionCloseR, goalR, goalR1
   , axiomAR, axiomBR, axiomCR, axiomACloseR, axiomBCloseR, axiomCCloseR
   , mpForwardR, mpMiddle1R, mpMiddle2R, mpCloseR
   , dedForwardR, dedBackwardR, dedCloseR, renumberR
     -- misc
   , createGoal, forward, createGoal1
   , nRef, n1Ref, n2Ref, n3Ref
   , phiRef, psiRef, chiRef
   , stRef, asRef
   -- tijdelijk, om buggy rules te testen
   , assumption, modusPonensForward, exProof
   ) where

import Ideas.Utils.Prelude   
import Data.Maybe
import Control.Monad
import Domain.Logic.Formula
import Domain.Logic.Parser
import Domain.Logic.LinearProof
import Domain.Logic.Axiomatic.Statement
import Ideas.Common.Library hiding (label)
import qualified Data.Set as S

instance Read SLogic where
   readsPrec _ s =
      case parseLogicPars s of
         Left _  -> []
         Right p -> [(p, "")]

instance Reference SLogic
 
----------------------------------------------------------------------
-- Axiom identifiers

logax :: Id
logax = newId "logic.propositional.axiomatic"

assumptionId, assumptionCloseId :: Id
assumptionId = describe "Introduces an assumption (phi)." $ 
   logax # "assumption"
assumptionCloseId = describe "Motivates an assumption (as|- phi)." $ 
   assumptionId # "close"


axiomAId, axiomBId, axiomCId, axiomACloseId, axiomBCloseId, axiomCCloseId  :: Id
axiomAId = describe "Introduces an instance of Axiom A (phi, psi)." $ 
   logax # "axiom-a"
axiomBId = describe "Introduces an instance of Axiom B (phi, psi, chi)." $ 
   logax # "axiom-b"
axiomCId = describe "Introduces an instance of Axiom C (phi, psi)." $ 
   logax # "axiom-c"   
axiomACloseId = describe "Motivates an instance of Axiom A (phi, psi)." $ 
   axiomAId # "close"
axiomBCloseId = describe "Motivates an instance of Axiom B (phi, psi, chi)." $ 
   axiomBId # "close"
axiomCCloseId = describe "Motivates an instance of Axiom C (phi, psi)." $ 
   axiomCId # "close" 

mpId, mpForwardId, mpMiddle1Id, mpMiddle2Id, mpCloseId :: Id
mpId = describe "Modus ponens" $ 
   logax # "modusponens"
mpForwardId = describe "Modus ponens applied to phi and phi -> psi." $ 
   mpId # "forward"
mpMiddle1Id = describe "Modus ponens: phi and psi are given (phi -> psi is derived)." $ 
   mpId # "middle1"
mpMiddle2Id = describe "Modus ponens: phi -> psi and psi are given (phi is derived)." $ 
   mpId # "middle2"
mpCloseId = describe "Modus ponens: phi, phi -> psi, and psi are given." $ 
   mpId # "close"

dedId, dedForwardId, dedBackwardId, dedCloseId :: Id
dedId = describe "Deduction rule" $ 
   logax # "deduction"
dedForwardId = describe "Deduction rule applied to phi, As |- psi." $ 
   dedId # "forward"
dedBackwardId = describe "Deduction rule applied to As |- phi -> psi." $ 
   dedId # "backward" 
dedCloseId = describe "Deduction rule applied to (phi, As |- psi) and (As |- phi -> psi)." $ 
   dedId # "close" 

goalId :: Id
goalId = describe "Introduces at line n a new goal st" $ 
   logax # "goal" 

goalId1 :: Id
goalId1 = describe "Introduces a new goal." $ 
   logax # "goal1"   
   
phiRef, psiRef, chiRef :: Ref SLogic
phiRef = makeRef "phi"
psiRef = makeRef "psi"
chiRef = makeRef "chi"

stRef :: Ref Statement
stRef = makeRef "st"

asRef :: Ref [SLogic]
asRef = makeRef "as"

nRef, n1Ref, n2Ref, n3Ref :: Ref Int
nRef   = makeRef "n"
n1Ref  = makeRef "n1"
n2Ref  = makeRef "n2"
n3Ref  = makeRef "n3"

----------------------------------------------------------------------
-- Parameterized rules

assumptionR :: Rule (Proof Statement)
assumptionR = ruleTrans assumptionId $ 
   transInput1 phiRef $ \x -> Just . assumption x
   
assumptionCloseR :: Rule (Proof Statement)
assumptionCloseR = ruleTrans assumptionCloseId $ 
   transInput1 nRef assumptionClose

axiomAR :: Rule (Proof Statement)
axiomAR = ruleTrans axiomAId $
   transInput2 phiRef psiRef $ \x y -> Just . introAxiomA x y
   
axiomACloseR :: Rule (Proof Statement)
axiomACloseR = ruleTrans axiomACloseId $
   transInput1 nRef axiomAClose

axiomBR :: Rule (Proof Statement)
axiomBR = ruleTrans axiomBId $
   transInput3 phiRef psiRef chiRef $ \x y z -> Just . introAxiomB x y z
 
axiomBCloseR :: Rule (Proof Statement)
axiomBCloseR = ruleTrans axiomBCloseId $
   transInput1 nRef axiomBClose
   
axiomCR :: Rule (Proof Statement)
axiomCR = ruleTrans axiomCId $
   transInput2 phiRef psiRef $ \x y -> Just . introAxiomC x y
   
axiomCCloseR :: Rule (Proof Statement)
axiomCCloseR = ruleTrans axiomCCloseId $
   transInput1 nRef axiomCClose

mpForwardR :: Rule (Proof Statement)
mpForwardR = siblingOf mpId $ ruleTrans mpForwardId $
   transInput2 n1Ref n2Ref modusPonensForward

mpMiddle1R :: Rule (Proof Statement)
mpMiddle1R = siblingOf mpId $ ruleTrans mpMiddle1Id $
   transInput2 n1Ref n2Ref modusPonensMiddle1

mpMiddle2R :: Rule (Proof Statement)
mpMiddle2R = siblingOf mpId $ ruleTrans mpMiddle2Id $
   transInput2 n1Ref n2Ref modusPonensMiddle2

mpCloseR :: Rule (Proof Statement)
mpCloseR = siblingOf mpId $ ruleTrans mpCloseId $
   transInput3 n1Ref n2Ref n3Ref modusPonensClose

dedForwardR :: Rule (Proof Statement)
dedForwardR = siblingOf dedId $ ruleTrans dedForwardId $
   transInput2 nRef phiRef deductionForward

dedBackwardR :: Rule (Proof Statement)
dedBackwardR = siblingOf dedId $ ruleTrans dedBackwardId $
   transInput1 nRef deductionBackward

dedCloseR :: Rule (Proof Statement)
dedCloseR = siblingOf dedId $ ruleTrans dedCloseId $
   transInput2 n1Ref n2Ref deductionClose

goalR1 :: Rule (Proof Statement)
goalR1 = ruleTrans goalId1 $
   transInput1 stRef createGoal1
   
goalR :: Rule (Proof Statement)
goalR = ruleTrans goalId $
   transInput2 nRef stRef createGoal

renumberR :: Rule (Proof Statement)
renumberR = describe "Renumber proof lines" $
   makeRule (logax # "renumber") $ \p -> Just (renumber p)

-----------------------------------------------------------------------

assumption :: SLogic -> Proof Statement -> Proof Statement
assumption phi = forward ([phi] |- phi) (unqualified assumptionId, [])

introAxiomA :: SLogic -> SLogic -> Proof Statement -> Proof Statement
introAxiomA phi psi = forward (axiomA phi psi) (unqualified axiomAId, [])

introAxiomB :: SLogic -> SLogic -> SLogic -> Proof Statement -> Proof Statement
introAxiomB phi psi chi = forward (axiomB phi psi chi) (unqualified axiomBId, [])

introAxiomC :: SLogic -> SLogic -> Proof Statement -> Proof Statement
introAxiomC phi psi = forward (axiomC phi psi) (unqualified axiomCId, [])

{-
--     A |- phi
--     B |- phi -> psi
-- A,B,C |- psi
modusPonensFits :: Statement -> Statement -> Statement -> Bool
modusPonensFits st1 st2 st3 =
   (assumptions st1 `S.union` assumptions st2) `S.isSubsetOf` assumptions st3
   && fits (consequent st1) (consequent st2) (consequent st3)
 where
   fits phi1 (phi2 :->: psi1) psi2 = phi1 == phi2 && psi1 == psi2
   fits _ _ _ = False
-}

assumptionClose :: Int -> Proof Statement -> Maybe (Proof Statement)
assumptionClose n prf = do
   st <- findNumber n prf >>= term
   let as = assumptions st
       cs = consequent st
   guard $ cs `S.member` as
   let  mot = ("assumption", [])
   return  $ addMotivation n mot prf   
   
axiomAClose :: Int -> Proof Statement -> Maybe (Proof Statement)
axiomAClose n prf = do
   st <- findNumber n prf >>= term
   let cs = consequent st      
   guard $ isAxiom cs 
   let  mot = ("axiom-a", [])
   return  $ addMotivation n mot prf  
 where 
   isAxiom (p :->: (q :->: r)) = p == r 
   isAxiom _ = False
   
axiomBClose :: Int -> Proof Statement -> Maybe (Proof Statement)
axiomBClose n prf = do
   st <- findNumber n prf >>= term
   let cs = consequent st      
   guard $ isAxiom cs 
   let  mot = ("axiom-b", [])
   return  $ addMotivation n mot prf  
 where 
   isAxiom ((p :->: (q :->: r)):->: ((s:->:t) :->: (u :->:v))) = p == s && p == u && q == t && r == v
   isAxiom _ = False 
   
axiomCClose :: Int -> Proof Statement -> Maybe (Proof Statement)
axiomCClose n prf = do
   st <- findNumber n prf >>= term
   let cs = consequent st      
   guard $ isAxiom cs 
   let  mot = ("axiom-c", [])
   return  $ addMotivation n mot prf  
 where 
   isAxiom ((p :->:q) :->:  (r :->: s)) = p == (Not s) && q == (Not r)
   isAxiom _ = False   

modusPonensForward :: Int -> Int -> Proof Statement -> Maybe (Proof Statement)
modusPonensForward n1 n2 prf = do
   st1 <- findNumber n1 prf >>= term
   st2 <- findNumber n2 prf >>= term
   psi <- fits (consequent st1) (consequent st2)
   let st  = assumptions st1 `S.union` assumptions st2 :|- psi
       mot = (show mpForwardId, [n1, n2])
   return (forwardAfter (max n1 n2) st mot prf)
 where
   fits (p :->: q) r | p == r = Just q
   fits p (q :->: r) | p == q = Just r
   fits _ _ = Nothing

{- first create assumption, axiom, or goal for the phi
modusPonensBackward :: Int -> SLogic -> Proof Statement -> Maybe (Proof Statement)
modusPonensBackward n phi prf = do
   pl  <- findNumber n prf
   guard (null (label pl))
   st1 <- term pl
   let (n1, n2) = nextNumberDecr2 prf
       new1 = goalNr n1 (assumptions st1 :|- phi)
       new2 = goalNr n2 (assumptions st1 :|- phi :->: consequent st1)
       mot = (mpLabel, [n1, n2])
   return $ insert new1 $ insert new2 $ addMotivation n mot prf
-}

modusPonensMiddle1 :: Int -> Int -> Proof Statement -> Maybe (Proof Statement)
modusPonensMiddle1 n m prf = do
   pl  <- findNumber n prf
   st1 <- term pl
   st2 <- findNumber m prf >>= term
   guard  $ (null (label pl)) && ((assumptions st2) `S.isSubsetOf` (assumptions st1))
   let psi = consequent st2 :->: consequent st1
       n1  = prevNumberBefore n prf
       new = goalNr n1 (assumptions st1 :|- psi)
       mot = (show mpMiddle1Id, [n1, m])
   return $ new <> addMotivation n mot prf
   
modusPonensMiddle2 :: Int -> Int -> Proof Statement -> Maybe (Proof Statement)
modusPonensMiddle2 n m prf = do
   pl  <- findNumber n prf
   st1 <- term pl
   st2 <- findNumber m prf >>= term
   guard  $ (null (label pl)) && ((assumptions st2) `S.isSubsetOf` (assumptions st1))
   psi <- fits (consequent st1) (consequent st2)
   let n1 = prevNumberBefore n prf
       new  = goalNr n1 (assumptions st1 :|- psi)
       mot = (show mpMiddle2Id, [n1, m])
   return $ new <> addMotivation n mot prf 
 where
   fits q (p :->: r)  | q == r = Just p
   fits _ _= Nothing
   
modusPonensClose :: Int -> Int -> Int -> Proof Statement -> Maybe (Proof Statement)
modusPonensClose n1 n2 n3 prf = do
   pl  <- findNumber n1 prf
   st1 <- term pl
   st2 <- findNumber n2 prf >>= term
   st3 <- findNumber n3 prf >>= term
   guard  $ (null (label pl)) && (((assumptions st2) `S.isSubsetOf` (assumptions st1)) && ((assumptions st3) `S.isSubsetOf` (assumptions st1)))
   guard $ fits (consequent st1) (consequent st2) (consequent st3)
   let  mot = (show mpCloseId, [n2, n3])
   return  $ addMotivation n1 mot prf 
 where
   fits q (p :->: r) (s :->: t) =  (q == r && p == (s :->: t)) ||(q == t && s == (p :->: q))
   fits q (p :->: r) s  = q == r && p == s
   fits q s (p :->: r) = q == r && p == s
   fits _ _ _ = False

deductionForward :: Int -> SLogic -> Proof Statement -> Maybe (Proof Statement)
deductionForward n phi prf = do
   st1 <- findNumber n prf >>= term
   let st  = (phi `S.delete` assumptions st1) :|- (phi :->: consequent st1)
       mot = (show dedForwardId, [n])
   return (forwardAfter n st mot prf)

deductionBackward :: Int -> Proof Statement -> Maybe (Proof Statement)
deductionBackward n prf = do
   pl  <- findNumber n prf
   st1 <- term pl
   guard (null (label pl))
   (phi, psi) <- isImpl (consequent st1)
   let n1  = prevNumberBefore n prf
       new = goalNr n1 (S.insert phi (assumptions st1) :|- psi)
       mot = (show dedBackwardId, [n1])
   return $ new <> addMotivation n mot prf
 where
   isImpl (p :->: q) = Just (p, q)
   isImpl _ = Nothing

deductionClose :: Int -> Int -> Proof Statement -> Maybe (Proof Statement)
deductionClose n1 n2 prf = do
   pl1 <- findNumber n1 prf
   st1 <- term pl1
   pl2 <- findNumber n2 prf
   st2 <- term pl2
   p   <- fits (consequent st1) (consequent st2)
   guard ((assumptions st2) == (S.delete p (assumptions st1)))
   let  mot = (show dedCloseId, [n1])
   return  $ addMotivation n2 mot prf 
 where
   fits q1 (p :->: q2) | q1 == q2 = Just p
   fits _ _ = Nothing

{- see modus ponens close
close :: Int -> Int -> Proof Statement -> Maybe (Proof Statement)
close n1 n2 prf | n1 < n2 = do
   pl1 <- findNumber n1 prf
   st1 <- term pl1
   pl2 <- findNumber n2 prf
   st2 <- term pl2
   guard (hasMotivation pl1 && not (hasMotivation pl2) && st1 `subStatement` st2)
   return (addMotivation n2 (motivation pl1) prf)
close n1 n2 prf 
   | n1 > n2   = close n2 n1 prf
   | otherwise = Nothing -}
   
createGoal1 :: Statement -> Proof Statement -> Maybe (Proof Statement)
createGoal1 st prf 
   | validStatement st = Just $ goalNr (prevNumber prf) st <> prf
   | otherwise = Nothing

createGoal :: Int -> Statement -> Proof Statement -> Maybe (Proof Statement)
createGoal n st prf 
   | validStatement st = Just $ goalNr n st <> prf
   | otherwise = Nothing
--------------------------------------------------------------------------------

forward :: Statement -> Motivation -> Proof Statement -> Proof Statement
forward st m prf = pl <> prf
 where
   n  = nextNumber prf
   pl = prooflineNr n st m
   
forwardAfter :: Int -> Statement -> Motivation -> Proof Statement -> Proof Statement
forwardAfter n1 st m prf = pl <> prf
 where
   n  = nextNumberAfter n1 prf
   pl = prooflineNr n st m

-- follows from deduction
axiomA :: SLogic -> SLogic -> Statement
axiomA phi psi = S.empty :|- phi :->: (psi :->: phi)

-- follows from deduction
axiomB :: SLogic -> SLogic -> SLogic -> Statement
axiomB phi psi chi = S.empty :|- (phi :->: (psi :->: chi)) :->: ((phi :->: psi) :->: (phi :->: chi))

axiomC :: SLogic -> SLogic -> Statement
axiomC phi psi = S.empty :|- (Not phi :->: Not psi) :->: (psi :->: phi)
{-
nextNumberDecr2 :: Proof a -> (Int, Int)
nextNumberDecr2 proof = 
   case filter (`notElem` usedNumbers proof) [1000, 999 ..] of
      n1:n2:_ -> (n1, n2)
      _ -> error "We need more numbers!"

main :: IO ()   
main = print exProof
-}
exProof :: Proof Statement
exProof = fromJust (make mempty)
 where
   make =
   {-
        return . createGoal ([p :->: q] |- (r :->: p) :->: (r :->: q))
    >=> deductionBackward 1000
    >=> deductionBackward 999
    >=> return . assumption r
    >=> return . assumption (r :->: p)
    >=> modusPonensForward 2 1
    >=> return . assumption (p :->: q)
    >=> modusPonensClose 998 3 4
--    >=> modusPonensForandBackward 998 4
 --   >=> modusPonensBackward 998 p
  --  >=> close 4 996
 --   >=> close 997 3
 -}
 
       createGoal1 ([]|- p:->:p)
    >=> createGoal 500 ([p, p :->:q ] |- q)  
  --  >=> return.assumption (p :->:p)
 --   >=> return.assumption p 
    >=> deductionBackward 1000
  --  >=> modusPonensForward 2 1
  --  >=> mpCloseBug1 3 1000
       
   p = Var (ShowString "p")
   q = Var (ShowString "q")
   r = Var (ShowString "r")
{-
go :: (Proof Statement)
go = fromJust $ fromJSON (toJSON exProof) -}