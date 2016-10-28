{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Domain.Logic.Axiomatic.Rules 
   ( assumptionId, axiomAId, axiomBId, axiomCId, mpId, dedId
   -- rules 
   , assumptionR, goalR
   , axiomAR, axiomBR, axiomCR
   , mpForwardR, mpMiddle1R, mpMiddle2R, mpCloseR
   , dedForwardR, dedBackwardR, dedCloseR, renumberR
     -- misc
   , createGoal, forward, mustHaveParameters
   ) where

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

assumptionId :: Id
assumptionId = describe "Introduces an assumption (phi)." $ 
   logax # "assumption"

axiomAId, axiomBId, axiomCId :: Id
axiomAId = describe "Introduces an instance of Axiom A (phi, psi)." $ 
   logax # "axiom-a"
axiomBId = describe "Introduces an instance of Axiom B (phi, psi, chi)." $ 
   logax # "axiom-b"
axiomCId = describe "Introduces an instance of Axiom C (phi, psi)." $ 
   logax # "axiom-c"   

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
goalId = describe "Introduces a new goal." $ 
   logax # "goal" 

----------------------------------------------------------------------
-- Parameterized rules

mustHaveParameters :: ParamTrans b a -> b -> Transformation a
mustHaveParameters f b = supplyParameters f (const (Just b))

assumptionR :: Rule (Proof Statement)
assumptionR = ruleTrans assumptionId $ mustHaveParameters f T
 where
   f = parameter1 "phi" (transPure . assumption)

axiomAR :: Rule (Proof Statement)
axiomAR = ruleTrans axiomAId $ supplyParameters f (\_ -> Just (T, T))
 where
   f = parameter2 "phi" "psi" $ \x y -> transPure (introAxiomA x y)

axiomBR :: Rule (Proof Statement)
axiomBR = ruleTrans axiomBId $ mustHaveParameters f (T, T, T)
 where
   f = parameter3 "phi" "psi" "chi" $ \x y z -> transPure (introAxiomB x y z)
   
axiomCR :: Rule (Proof Statement)
axiomCR = ruleTrans axiomCId $ mustHaveParameters f (T, T)
 where
   f = parameter2 "phi" "psi" $ \x y -> transPure (introAxiomC x y)

mpForwardR :: Rule (Proof Statement)
mpForwardR = siblingOf mpId $ ruleTrans mpForwardId $ mustHaveParameters f (0, 0)
 where
   f = parameter2 "n1" "n2" $ \x y -> makeTrans (modusPonensForward x y)

mpMiddle1R :: Rule (Proof Statement)
mpMiddle1R = siblingOf mpId $ ruleTrans mpMiddle1Id $ mustHaveParameters f (0, 0)
 where
   f = parameter2 "n1" "n2" $ \x y -> makeTrans (modusPonensMiddle1 x y)

mpMiddle2R :: Rule (Proof Statement)
mpMiddle2R = siblingOf mpId $ ruleTrans mpMiddle2Id $ mustHaveParameters f (0, 0)
 where
   f = parameter2 "n1" "n2" $ \x y -> makeTrans (modusPonensMiddle2 x y)

mpCloseR :: Rule (Proof Statement)
mpCloseR = siblingOf mpId $ ruleTrans mpCloseId $ mustHaveParameters f (0, 0, 0)
 where
   f = parameter3 "n1" "n2" "n3" $ \x y z -> makeTrans (modusPonensClose x y z)

dedForwardR :: Rule (Proof Statement)
dedForwardR = siblingOf dedId $ ruleTrans dedForwardId $ mustHaveParameters f (0, T)
 where
   f = parameter2 "n" "phi" $ \x y -> makeTrans (deductionForward x y)

dedBackwardR :: Rule (Proof Statement)
dedBackwardR = siblingOf dedId $ ruleTrans dedBackwardId $ mustHaveParameters f 0
 where
   f = parameter1 "n" $ \x -> makeTrans (deductionBackward x)

dedCloseR :: Rule (Proof Statement)
dedCloseR = siblingOf dedId $ ruleTrans dedCloseId $ mustHaveParameters f (0, 0)
 where
   f = parameter2 "n1" "n2" $ \x y -> makeTrans (deductionClose x y)

goalR :: Rule (Proof Statement)
goalR = ruleTrans goalId $ mustHaveParameters f ([] |- T)
 where
   f = parameter1 "st" $ \x -> transMaybe (createGoal x)

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


modusPonensForward :: Int -> Int -> Proof Statement -> Maybe (Proof Statement)
modusPonensForward n1 n2 prf = do
   st1 <- findNumber n1 prf >>= term
   st2 <- findNumber n2 prf >>= term
   psi <- fits (consequent st1) (consequent st2)
   let st  = assumptions st1 `S.union` assumptions st2 :|- psi
       mot = (show mpForwardId, [n1, n2])
   return (forward st mot prf)
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
       n1  = nextNumberDecr prf
       new = goalNr n1 (assumptions st1 :|- psi)
       mot = (show mpMiddle1Id, [n1, m])
   return $ insert new  $ addMotivation n mot prf
   
modusPonensMiddle2 :: Int -> Int -> Proof Statement -> Maybe (Proof Statement)
modusPonensMiddle2 n m prf = do
   pl  <- findNumber n prf
   st1 <- term pl
   st2 <- findNumber m prf >>= term
   guard  $ (null (label pl)) && ((assumptions st2) `S.isSubsetOf` (assumptions st1))
   psi <- fits (consequent st1) (consequent st2)
   let n1 = nextNumberDecr prf
       new  = goalNr n1 (assumptions st1 :|- psi)
       mot = (show mpMiddle2Id, [n1, m])
   return $ insert new  $ addMotivation n mot prf 
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
   return (forward st mot prf)

deductionBackward :: Int -> Proof Statement -> Maybe (Proof Statement)
deductionBackward n prf = do
   pl  <- findNumber n prf
   st1 <- term pl
   guard (null (label pl))
   (phi, psi) <- isImpl (consequent st1)
   let n1  = nextNumberDecr prf
       new = goalNr n1 (S.insert phi (assumptions st1) :|- psi)
       mot = (show dedBackwardId, [n1])
   return $ insert new $ addMotivation n mot prf
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
   
createGoal :: Statement -> Proof Statement -> Maybe (Proof Statement)
createGoal st prf 
   | validStatement st = Just (insert (goalNr (nextNumberDecr prf) st) prf)
   | otherwise = Nothing

--------------------------------------------------------------------------------

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

-- follows from deduction
axiomA :: SLogic -> SLogic -> Statement
axiomA phi psi = S.empty :|- phi :->: (psi :->: phi)

-- follows from deduction
axiomB :: SLogic -> SLogic -> SLogic -> Statement
axiomB phi psi chi = S.empty :|- (phi :->: (psi :->: chi)) :->: ((phi :->: psi) :->: (phi :->: chi))

axiomC :: SLogic -> SLogic -> Statement
axiomC phi psi = S.empty :|- (Not phi :->: Not psi) :->: (psi :->: phi)

nextNumberDecr :: Proof a -> Int
nextNumberDecr proof = head (filter (`notElem` usedNumbers proof) [1000, 999 ..])

{-
nextNumberDecr2 :: Proof a -> (Int, Int)
nextNumberDecr2 proof = 
   case filter (`notElem` usedNumbers proof) [1000, 999 ..] of
      n1:n2:_ -> (n1, n2)
      _ -> error "We need more numbers!"

main :: IO ()   
main = print exProof

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
 
       createGoal ([ p:->:p ]|- p:->:p)
    >=> return.assumption (p :->:p)
    >=> return.assumption p 
    >=> modusPonensForward 2 1
    >=> deductionClose 3 1000
       
   p = Var (ShowString "p")
   q = Var (ShowString "q")
   r = Var (ShowString "r")

go :: (Proof Statement)
go = fromJust $ fromJSON (toJSON exProof) -}