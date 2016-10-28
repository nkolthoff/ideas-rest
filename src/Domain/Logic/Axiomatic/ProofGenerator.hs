module Domain.Logic.Axiomatic.ProofGenerator where

import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S
import Ideas.Common.Utils (ShowString(..))
import Ideas.Common.Library hiding (label)
import qualified Ideas.Common.Library as Library
import Domain.Logic.Formula
import Domain.Logic.Parser
import Domain.Logic.LinearProof hiding (addAssumption)
import Domain.Logic.Axiomatic.Statement
import Domain.Logic.Axiomatic.Examples

axiomaticExercise :: Exercise Env
axiomaticExercise = emptyExercise
   { exerciseId     = describe "Axiomatic proofs" $ 
                      newId "logic.propositional.axiomatic"
   , status         = Experimental
   , prettyPrinter  = show
   , strategy       = axiomaticStrategy
   , examples       = [ (dif, makeEnv a) | (dif, a) <- exampleList ]
   }    
   
axiomaticStrategy :: LabeledStrategy (Context Env)
axiomaticStrategy = Library.label "axiomatic" $
   (untilS stop 
      $  goalAvailable
 --     |> implicationIntroStep
      |> implicationIntro
      |> elimGoalStep
      |> elimGoal
   --   |> axiomBheuristic1 .*. repeatS (modusPonens)
   --   |> axiomBheuristic2 
      |> axiomCheuristic1 .*. repeatS (modusPonens)
      |> axiomCheuristic3 .*. repeatS (modusPonens)
      |> axiomCheuristic2 .*. repeatS (modusPonens)
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
      |> useImplAssumption
      |> useNegAssumption)
      .*. repeatS deleteUnusedLines
 where
   stop = maybe True (null . goals) . fromContext

-----------------------------------------------------------------
-- Sub-strategies

contradiction1S :: Strategy (Context Env)
contradiction1S =
   --   (contradiction1 .*. repeatS (modusPonens) .*. contradiction1seq .*. repeatS (modusPonens) |> implicationIntro |> elimGoal)
        (contradiction1 .*. repeatS (modusPonens) .*. contradiction1seq .*. repeatS (modusPonens))
contradiction2S :: Strategy (Context Env)
contradiction2S = contradiction2 .*. contradiction2seq .*. repeatS (modusPonens) .*. contradiction1S


-----------------------------------------------------------------
 
data Env = Env 
   { goals      :: [(Statement, Bool)]
   , availables :: Proof Statement
   , proof      :: Proof Statement
   }
 deriving Eq

showSet :: Show a => S.Set a -> String
showSet s = "{" ++ intercalate ", " (map show (S.toList s)) ++ "}"

getNr :: Proof a -> Int
getNr = fromMaybe 0 . number . last . prooflines

changeMotivation :: Statement -> Motivation -> Proof Statement -> Proof Statement
changeMotivation st0 mot = rec . prooflines
 where 
   rec [] = mempty
   rec (pl:prf)  
      | maybe False (subStatement st0) (term pl) && null (label pl) = 
           prooflineNr (fromMaybe 0 (number pl)) (fromJust (term pl)) mot 
           <> makeProof prf
      | otherwise = makeProof [pl] <> rec prf

makeProofEnv :: Proof Statement -> Env
makeProofEnv p = 
   makeEnv (fromJust (term (last (prooflines p))))

makeEnv :: Statement -> Env
makeEnv st@(ps :|- q) = Env 
   { goals       = [(st, True)]
   , availables  = mconcat [ makeAvail i p | (i, p) <- zip [1..] (S.toList ps) ]
   , proof       = goalNr 1 (ps :|- q)
   }
 where 
   makeAvail i p = prooflineNr i ([p] |- p) ("Assumption", [])
    
instance Show Env where
   show env = intercalate "\n"
      [ column "goals" 
           [showUsed b  (show st) | (st, b) <- goals env ]
      , column "availables" $ lines (show (availables env))
      , column "proof" $ lines (show (proof env))
      ]
    where
      column s xs = intercalate "\n" $ (s ++ ":") : map ("  " ++) xs

showUsed :: Bool -> String -> String
showUsed b = if b then (++ "  [used]") else id
 
mmsee :: Int -> IO ()
mmsee i = printDerivation axiomaticExercise (makeEnv $ snd $ mmExampleList !! i)

see :: Int -> IO ()
see i = printDerivation axiomaticExercise (makeEnv $ snd $ exampleList !! i)

seepp = printDerivation axiomaticExercise (Env { goals      = [(S.empty :|- Not p, False)] 
                                                  , availables = prooflineNr 1 (S.singleton (Not (Not p)):|- q) ("assumption", [])<> prooflineNr 2 (S.singleton (Not (Not p)):|- Not q)("assumption", [])
                                              , proof      = prooflineNr 1 (S.singleton (Not (Not p)):|- q) ("assumption", [])<> prooflineNr 2 (S.singleton (Not (Not p)):|- Not q)("assumption", [])})
          where   p = Var (ShowString "p") 
                  q = Var (ShowString "q")

modusPonens :: Rule (Context Env)
modusPonens = liftToContext $ makeRule "modus-ponens" trans
 where
   trans env
      | null fs   = Nothing
      | otherwise = Just env { availables = availables env <> new }
    where
      new = mconcat (zipWith ($) fs [nextNumber (availables env) ..])
      fs  = [ \i -> prooflineNr i st ("Modus Ponens", maybeToList (number pl1) ++ maybeToList (number pl2))
            | pl1 <- prooflines (availables env)
            , pl2 <- prooflines (availables env)
            , st  <- isMP (term pl1) (term pl2)
            , all (maybe True (\t -> not (t `subStatement` st)) . term) (prooflines (availables env))
            ]
                       
      isMP (Just (as1 :|- p1 :->: q)) (Just (as2 :|- p2)) | p1 == p2 =
         [ as1 `S.union` as2 :|- q ] 
      isMP _ _ = []
{-
-- rule if double negation is allowed as an extra theorem
doubleNegation :: Rule (Context Env)
doubleNegation = liftToContext $ makeRule "double-negation" trans
 where
   trans env 
      | null fs   = Nothing
      | otherwise = Just env { availables = availables env <> new }
    where
      new = mconcat (zipWith ($) fs [nextNumber (availables env) ..])
      fs  = [ \i -> prooflineNr i st ("Double Negation", maybeToList (number pl))
            | pl <- prooflines (availables env) 
            , st <- isDoubleNeg (term pl)
            , all (maybe True (\t -> not (t `subStatement` st)) . term) (prooflines (availables env))
            ] 
            
      isDoubleNeg (Just (as :|- Not (Not p))) = return (as :|- p)
      isDoubleNeg _ = []
-}  

doubleNegation :: Rule (Context Env)
doubleNegation = liftToContext $ makeRule "double-negation" trans
 where
   trans env 
      | null fs   = Nothing
      | otherwise = Just env { availables = availables env <> mconcat (take 3 new) }
    where
      new = mconcat (zipWith ($) fs (group3 [nextNumber (availables env) ..]))
      fs  =  [ \(i1, i2, i3) ->  
                  [ prooflineNr i1 axa  ("Axiom a", [])
                  , prooflineNr i2 axc1 ("Axiom c", [])
                  , prooflineNr i3 axc2 ("Axiom c", [])
                  ]
            | pl  <- prooflines (availables env) 
            , st <- maybeToList (term pl)
            , let con = consequent st
            , pcon <- isDoubleNeg con
            , let axa  = axiomA con (Not (Not con))
                  axc1 = axiomC (Not con) (Not pcon)
                  axc2 = axiomC pcon con   
            , all (maybe True (\t -> not (t `subStatement` (assumptions st :|- pcon))) . term) (prooflines (availables env))
            ] 
            
      isDoubleNeg (Not (Not p)) = [p]
      isDoubleNeg _ = []

-- follows from deduction
axiomA :: SLogic -> SLogic -> Statement
axiomA phi psi = S.empty :|- phi :->: (psi :->: phi)

-- follows from deduction
axiomB :: SLogic -> SLogic -> SLogic -> Statement
axiomB phi psi chi = S.empty :|- (phi :->: (psi :->: chi)) :->: ((phi :->: psi) :->: (phi :->: chi))

axiomC :: SLogic -> SLogic -> Statement
axiomC phi psi = S.empty :|- (Not phi :->: Not psi) :->: (psi :->: phi)

group3 :: [a] -> [(a, a, a)]
group3 (x:y:z:rest) = (x, y, z) : group3 rest
group3 _ = []

group4 :: [a] -> [(a, a, a, a)]
group4 (x:y:z:q:rest) = (x, y, z,q) : group4 rest
group4 _ = []

-- voegt een implicatie (via deductiestelling) toe aan de availables, en 
-- verwijdert de bijbehorende doelen
implicationIntro :: Rule (Context Env)
implicationIntro = liftToContext $ makeRule "impl-intro" trans
 where
   trans env@(Env ((csr, inpr):(as :|- p :->: q, _):gls) _ prf) 
      | not newIsEmpty && inpr && not (motivated (prooflines prf)) = Just env
           { goals = gls
           , availables = availables env <> new
           , proof = initProof subproof <> changeline (proof env)
           }
      | not newIsEmpty && not (motivated (prooflines prf)) = Just env
           { goals = gls
           , availables = availables env <> new
           , proof = subproof <> proof env
           }
      | not newIsEmpty && inpr = Just env -- this part of the rule is 'minor'
           { goals = gls
           , availables = availables env <> new
           }
    where
      qs  = [ \i -> prooflineNr i (S.delete p as1 :|- p :->: q1) ("Deduction", maybeToList (number pl)) 
            | pl <- prooflines (availables env)
            , (as1 :|- q1) <- maybeToList (term pl)
            , q1 == q
            , (as1 :|- q1) `subStatement` csr 
            ]
   
      new = mconcat $ zipWith ($) qs [nextNumber (availables env) .. ]
      newIsEmpty = null $ prooflines new
     
      subproof = 
         renumberFrom (nextNumber (proof env)) $
         stripProofBy (`subStatement` (assumptions csr :|- q)) (availables env)
   
      changeline = changeMotivation (as :|- q) (motivation (last (prooflines subproof)))
      motivated = any $ \pl -> 
         maybe False (`subStatement` csr) (term pl) && not (null (label pl))
   trans _ = Nothing
   

-- voegt een implicatie (via deductiestelling) toe aan de availables, en 
-- verwijdert de bijbehorende doelen en breidt stapsgewijs het bewijs uit
implicationIntroStep :: Rule (Context Env)
implicationIntroStep = liftToContext $ makeRule "impl-intro-step" trans
 where
   trans env@(Env ((csr, inpr):(as :|- p :->: q, inpr2):gls) _ prf)
      |   not newIsEmpty && cond  = Just env
           {
           goals = (as :|- p :->: q, inpr2):gls
           , availables = availables env <> new 
           } 
      | not newIsEmpty && inpr && inpr2 && cond2 && not (motivated (prooflines prf))  = Just env
           { 
             goals = gls
           , availables = availables env <> new             
           , proof = changeline (proof env)              
           }
      | not newIsEmpty && inpr && inpr2 && not cond3  = Just env
           { 
             proof = grounded  
                     <>  prooflineNr (nextNumber (proof env)) (head new1) (mot motoud)
                     <> ungrounded  
           }
      | not newIsEmpty && not inpr && not cond3 = Just env
           {  
             proof = grounded  
                     <>  prooflineNr (nextNumber (proof env)) (head new1) (mot motoud)
                     <> ungrounded  
           }
      | not newIsEmpty && inpr = Just env -- this part of the rule is 'minor'
           { goals = gls
           , availables = availables env <> new 
           }
    where
   
      qs  = [ \i -> prooflineNr i (S.delete p as1 :|- p :->: q1) ("Deduction", maybeToList (number pl)) 
            | pl <- prooflines (availables env)
            , (as1 :|- q1) <- maybeToList (term pl)
            , q1 == q
            , (as1 :|- q1) `subStatement` csr 
            ]
  -- <> prooflineNr (nextNumber (availables env)) (axiomC q p)  ("Axiom c",  [])
      new = mconcat $ zipWith ($) qs [nextNumber (availables env) .. ]
      newIsEmpty = null $ prooflines new
     
      subproof = 
         renumberFrom (nextNumber (proof env)) $
         stripProofBy (`subStatement` (assumptions csr :|- q)) (availables env)
      grounded = groundedProof (proof env) 
      ungrounded = unGroundedProof (proof env)
      new1 = filter  (noSubstatementInProof grounded) [ st| pl <- (prooflines subproof)
                                                   , st <- maybeToList (term pl)]
      cond = null new1 
      cond2 = (head new1) `subStatement` (S.union (S.singleton p) as :|-  q)
      cond3 = null (prooflines ungrounded)
      nrs = head [ maybeToList (number pl1) ++ maybeToList (number pl2)
                     | pl1 <- prooflines (grounded)
                     , pl2 <- prooflines (grounded)
                     , isMP (term pl1) (term pl2)
                     ] 
                  where
                      isMP (Just (cs1 :|- (p1 :->: p2))) (Just (cs2 :|- q)) = (p1 == q) && (p2 == consequent ((head new1)))  && ((S.union cs1 cs2) `S.isSubsetOf` (assumptions (head new1)))
                      isMP _ _                                = False
                      
      nr = head [ maybeToList (number pl)
                     | pl <- prooflines (grounded)
                     , isDed (term pl)  (head new1)
                     ] 
                  where
                      isDed (Just (cs1 :|- q )) (cs2 :|- (r :->: s)) =  s == q  && ((S.delete r cs1) `S.isSubsetOf` cs2)
                      isDed _ _                              = False
      
      motoud = motivation $ fromJust $ findInProof (head new1) subproof
      mot ( "Modus Ponens", _) = ( "Modus Ponens", nrs)
      mot ("Deduction", [n]) = ("Deduction", nr)
      mot  _                   = motoud       

  

 
      changeline = changeMotivation (as :|- q) (mot (motivation (last (prooflines subproof))))
       
      motivated = any $ \pl -> 
         maybe False (`subStatement` csr) (term pl) && not (null (label pl))
   trans _ = Nothing
   


-- bewijs een doel mbv deductiestelling: voeg doel toe en voeg regels  toe aan 
-- het bewijs, als die er niet al in staan
deduction :: Rule (Context Env)
deduction = liftToContext $ makeRule "deduction" trans
 where
   trans env@(Env ((st@(as :|- p :->: q), inpr):gls) _ _) 
      | maybe False (== st) (term pl) = Just env 
           { goals = (newst, True):(st, True):gls
           , availables = availables env <> avp
           , proof = let n = nextNumber (proof env) in
                     goalNr n newst
                  <> prooflineNr (fromMaybe 0 (number pl)) st ("Deduction", [n])
                  <> prf
           }
      | inpr = Just env 
           {  goals = (newst, True):(st, True):gls
           }   
      | otherwise = Just env 
           { goals = (newst, True):(st, True):gls
           , availables = availables env <> avp
           , proof = let n = nextNumber (proof env) in
                     groundedProof (proof env)
                  <> goalNr (n+1) newst
                  <> prooflineNr n st ("Deduction", [n+1])
                  <> unGroundedProof (proof env)
           }
    where
      avp   = prooflineNr (nextNumber (availables env)) ([p] |- p) ("Assumption", [])
      newst = addAssumption p (as :|- q)
      (pl, prf) = headTailProof (proof env)
   trans _ = Nothing

   
 --       grounded = groundedProof (proof env) 
  --    ungrounded = unGroundedProof (proof env)
-- doel bereikt: voeg motivatie toe als regel al in het bewijs staat, voeg 
-- anders regel + motivatie toe
elimGoal :: Rule (Context Env)
elimGoal = liftToContext $ makeRule "elim-goal" trans
 where
   trans env@(Env ((as :|- p, inpr):gls) _ _)
      |  reached &&  inpr = Just env
   --   reached && consIsP  = Just env 
           { goals = gls 
          , proof = initProof subproof <> 
                    changeMotivation (head reachedSt) mot (proof env)
                     
           }
      | reached && not inpr = Just env 
           { goals = gls
           , proof = subproof <> proof env
           }
    where
      reachedSt =
         let ok2 (bs :|- q) = p == q && bs `S.isSubsetOf` as
         in filter ok2 (mapMaybe term (prooflines (availables env)))
      reached = not (null reachedSt)
      
      subproof = 
         renumberFrom (nextNumber (proof env)) $ 
         stripProof (head reachedSt) (availables env)
      mot = motivation $ fromJust $ findInProof (head reachedSt) subproof
      pl = head (prooflines (proof env))
      consIsP = maybe False ((== p) . consequent) (term pl)
   trans _ = Nothing

elimGoalStep :: Rule (Context Env)
elimGoalStep = liftToContext $ makeRule "elim-goal-step" trans
 where
   trans env@(Env ((as :|- p, inpr):gls) _ _)
      |  reached && cond  = Just env
           {goals = gls}    
      |  reached &&  inpr && cond2 = Just env
           { goals = gls 
          , proof =  changeMotivation (head reachedSt) (mot motoud)(proof env)
                     
           }
      |  reached = Just env
           {   proof = grounded 
                <>  prooflineNr (nextNumber (proof env)) (head new) (mot motoud)
                <> ungrounded                                      
           }
 
    where
      reachedSt =
         let ok2 (bs :|- q) = p == q && bs `S.isSubsetOf` as
         in filter ok2 (mapMaybe term (prooflines (availables env)))
      reached = not (null reachedSt)
      nrs = head [ maybeToList (number pl1) ++ maybeToList (number pl2)
                     | pl1 <- prooflines (grounded)
                     , pl2 <- prooflines (grounded)
                     , isMP (term pl1) (term pl2)
                     ] 
                  where
                      isMP (Just (cs1 :|- (p1 :->: p2))) (Just (cs2 :|- q)) = (p1 == q) && (p2 == consequent ((head new)))  && ((S.union cs1 cs2) `S.isSubsetOf` (assumptions (head new)))
                      isMP _ _                                = False
                      
      nr = head [ maybeToList (number pl)
                     | pl <- prooflines (grounded)
                     , isDed (term pl)  (head new)
                     ] 
                  where
                      isDed (Just (cs1 :|- q )) (cs2 :|- (r :->: s)) =  s == q  && ((S.delete r cs1) `S.isSubsetOf` cs2) -- && (r `S.member` cs1)
                      isDed _ _                              = False
      subproof = 
         renumberFrom (nextNumber (proof env)) $ 
         stripProof (head reachedSt) (availables env)
      grounded = groundedProof (proof env) 
      ungrounded = unGroundedProof (proof env)
      new = filter  (noSubstatementInProof grounded) [ st| pl <- (prooflines subproof)
                                                   , st <- maybeToList (term pl)]
      motoud = motivation $ fromJust $ findInProof (head new) subproof
      mot ( "Modus Ponens", _) = ( "Modus Ponens", nrs)
      mot ("Deduction", [n]) = ("Deduction", nr)
      mot  _                   = motoud       
                                     where
                                     nrs  = []
 
      cond =  null new
      cond2 = head new `subStatement` (as :|- p)
   trans _ = Nothing   
      
   
falseAsGoal :: Rule (Context Env)
falseAsGoal = liftToContext $ makeRule "false-goal" trans
 where
   trans env@(Env ((as :|- p@(Var _), _):_) _ _) 
      | p /= F = Just env
           { goals = (addAssumption (Not p) (as :|- F), False) : goals env
           , availables = availables env <> new
           }
    where
      new = prooflineNr (nextNumber (availables env)) (S.singleton (Not p) :|- Not p) ("Assumption", [])
   trans _ = Nothing

negAsGoal :: Rule (Context Env)
negAsGoal = liftToContext $ makeRule "neg-goal" trans
 where
   trans env@(Env ((as :|- Not p, _):(st@(bs :|- q), inpr):gls) _ _) | q/= F = Just env
      { goals = (addAssumption p (as :|- F), False) : goals env 
      , availables = availables env <> new
      }
      where
       new = prooflineNr (nextNumber (availables env)) (S.singleton p :|- p) ("Assumption", [])
   trans env@(Env ((as :|- Not p, _):gls) _ _)  = Just env
      {goals = (addAssumption p (as :|- F), False) : goals env 
      , availables = availables env <> new
      } 
     where
       new = prooflineNr (nextNumber (availables env)) (S.singleton p :|- p) ("Assumption", [])
   trans _ = Nothing

-- hulpstelling: bewijs dmv contradictie; als de tebewijzen formule al in het 
-- bewijs staat, voegt contradiction voor deze regel de contradictie toe, anders 
-- wordt boven aan het bewijs contradictie + conclusie toegevoegd
contradiction :: Rule (Context Env)
contradiction = liftToContext $ makeRule "contradiction" trans
 where
   trans env@(Env ((as :|- F, _):(st@(bs :|- p), inpr):gls) _ _) 
      | cond && inpr = Just env
           { goals = gls 
           , availables = availables env <> newav
           , proof = let (ms, ns) = break equaltogoal (prooflines (proof env))
                     in makeProof ms 
                     <> initProof subproof
                     <> changeline (makeProof ns)
           }
      | cond = Just env
           { goals = gls 
           , availables = availables env <> newav
           , proof = subproof <> proof env
           }
    where
      cond   = not (null new)
      newav  = head new
      contra = fromJust $ term $ head $ prooflines $ newav
      
      subproof = renumberFrom (nextNumber (proof env)) $
                 stripProof contra (availables env <> newav)
   
      new = [ prooflineNr (nextNumber (availables env)) (zs :|- p) 
                 ("Contradiction", mapMaybe number [pl1, pl2])
            | pl1 <- prooflines (availables env)
            , t1  <- maybeToList (term pl1)
            , pl2 <- prooflines (availables env)
            , t2  <- maybeToList (term pl2)
            , fits (consequent t1) (consequent t2)
            , let zs = S.delete (neg p)
                     $ S.union (assumptions t1) (assumptions t2), zs `S.isSubsetOf` bs 
            ]
     -- dit moet handiger kunnen            
      fits p1 (Not p2) = p1 == p2
      fits _ _ = False 
      
      neg (Not x) = x
      neg x       = Not x
      
      equaltogoal = maybe False (== st) . term
      changeline = changeMotivation st (motivation (last (prooflines subproof)))
   trans _ = Nothing

  
--   bewijs van p uit Not p -> p
contradiction1 :: Rule (Context Env)
contradiction1 = liftToContext $ makeRule "contradiction1" trans
 where
  trans env@(Env ((as :|- F, _):(st@(_ :|- p), inpr):gls) _ _) 
      | cond  = Just env
           { goals = (st, inpr):gls  
           , availables = availables env <> mconcat (take 4 newav)
           }
    where         
       cond = any (== (Not p :->: p))[ consequent st
                                                                                              | pl <- prooflines (availables env)
                                                                                              , st <- maybeToList (term pl)
                                                                                              , S.isSubsetOf (assumptions st) as ]  
       newav = mconcat (zipWith ($) fs (group4 [nextNumber (availables env) ..]))
       fs  =  [ \(i1, i2, i3, i4) ->  
                  [ prooflineNr i1 axa  ("Axiom a", [])
                  , prooflineNr i2 axc1 ("Axiom c", [])
                  , prooflineNr i3 axc2 ("Axiom c", [])
                  , prooflineNr i4 axb ("Axiom b", [])
                  ]
              |
                  let axa  = axiomA (Not p) (Not (Not (Not p :->: p)))
                      axc1 = axiomC  (Not (Not p :->: p)) ( p)
                      axc2 = axiomC p (Not p :->: p)   
                      axb  = axiomB (Not p) p (Not (Not p :->: p))
              ] 
  trans _ = Nothing    

 -- bewijs van |- Not p -> p uit Not p |- p
contradiction1a :: Rule (Context Env)
contradiction1a = liftToContext $ makeRule "contradiction1a" trans
 where
  trans env@(Env ((as :|- F, _):(st@(cs :|- p), inpr):gls) _ _) 
      | cond  = Just env
           { goals = (cs:|- Not p :->: p, False):(goals env)
           }
    where         
            cond = not(null new)     
            new = [pl1 
                      | pl1 <- prooflines (availables env)
                      , bs :|- q <- maybeToList (term pl1)
                      , q == p
                      , bs `S.isSubsetOf` as  && (Not p) `S.member` bs
                   ]
    

  trans _ = Nothing      
  
contradiction1seq :: Rule (Context Env)
contradiction1seq = liftToContext $ makeRule "contradiction1seq" trans
 where
  trans env@(Env((st@(_ :|- p), inpr):gls) _ _) 
          = Just env
           { goals = (st, inpr):gls
           , availables = availables env <> head newav
           }
    where         
        newav = [ prooflineNr (nextNumber (availables env)) (S.empty :|- (Not p) :->: (p :->: (Not (Not p :->: p)))) 
                 ("Deduction", mapMaybe number [pl])
                | pl <- prooflines (availables env)
                , (as1 :|- q1) <- maybeToList (term pl)
                , q1 == (p :->: (Not (Not p :->: p))) && as1 == S.singleton (Not p)
                ]
  trans _ = Nothing 
  
--  Bewijs van p uit Not p -> Not Not p 
contradiction2 :: Rule (Context Env)
contradiction2 = liftToContext $ makeRule "contradiction2" trans
 where
  trans env@(Env ((as :|- F, _):(st@(_ :|- p), inpr):gls) _ _) 
      | cond  = Just env
           {  
           availables = availables env <> newav
           }
    where         
       cond = any (== (Not  p :->: Not (Not p)))[ consequent st
                                                                                              | pl <- prooflines (availables env)
                                                                                              , st <- maybeToList (term pl)]  
       newav = prooflineNr (nextNumber (availables env)) (S.singleton (Not (Not p)) :|- Not (Not p)) 
                 ("Assumption",  [])
              
  trans _ = Nothing    
                     
contradiction2seq :: Rule (Context Env)
contradiction2seq = liftToContext $ makeRule "contradiction2seq" trans
 where
  trans env@(Env ((as :|- F, _):(st@(_ :|- p), inpr):gls) _ _) 
      | cond  = Just env
           {  
           availables = availables env <> newav
           }
    where         
       cond = any (== (Not  p :->: Not (Not p)))[ consequent st
                                                                                              | pl <- prooflines (availables env)
                                                                                              , st <- maybeToList (term pl)]  
       newav = prooflineNr (nextNumber (availables env)) (axiomC p (Not p)) 
                 ("Axiom C",  [])
              
  trans _ = Nothing    

-- bewijs van Not p uit p -> Not p  
contradiction3 :: Rule (Context Env)
contradiction3 = liftToContext $ makeRule "contradiction3" trans
 where
  trans env@(Env ((as :|- F, inpr1):((bs :|- Not p), inpr2):gls) _ _) 
      | cond  = Just env
           {goals = [(bs :|- Not (Not p) :->:  (Not p), False),(as :|- F, inpr1),((bs :|- Not p), inpr2) ] 
           }
    where         
       cond = any (== (  p :->:  (Not p)))[ consequent st
                                                                                              | pl <- prooflines (availables env)
                                                                                              , st <- maybeToList (term pl)]     
  trans _ = Nothing      


-- bewijs van Not p uit p |- q en |- Not q  
contradiction4 :: Rule (Context Env)
contradiction4 = liftToContext $ makeRule "contradiction4" trans
 where
  trans env@(Env ((as :|- F, inpr1):((bs :|- Not p), inpr2):gls) _ _) 
      | cond1 = Just env
           { goals = [( bs :|-  (Not (Not p)):->:  (Not (Not q)), False)
                    ,( bs :|-   (Not q):->:   (Not p), False)  
                    ,((bs :|- Not p), inpr2) ] <> gls
           , availables = availables env <> newav1 
           }
      | cond  = Just env
           { goals = [(S.union bs (S.singleton (Not (Not p))) :|- q, False)
                    , (S.empty  :|- (Not(Not (Not q))) :->: Not q, False)
                    , (as :|- F, inpr1)
                    , ((bs :|- Not p), inpr2)] <> gls
                    
           , availables = availables env <> newav 
           }
    where         
      cond1 = cond && any (== (  S.empty  :|- (Not(Not (Not q))) :->: Not q))[ st
                                                                             | pl <- prooflines (availables env)
                                                                             , st <- maybeToList (term pl)]
      cond = not(null new)
      q = consequent (head new)
      new = [ t1
            | pl1 <- prooflines (availables env)
            , t1  <- maybeToList (term pl1)
            , pl2 <- prooflines (availables env)
            , t2  <- maybeToList (term pl2)
            , fits (consequent t1) (consequent t2)
            , let zs =  S.union (S.delete p (assumptions t1)) (assumptions t2), zs `S.isSubsetOf` bs 
            ]
      newav1 = prooflineNr (nextNumber (availables env)) (axiomC (Not(Not q)) q)
                 ("Axiom c",  [])        
      fits p1 (Not p2) = p1 == p2
      fits _ _ = False 
      newav = prooflineNr (nextNumber (availables env)) (S.singleton (Not (Not p)) :|- Not (Not p)) 
                 ("Assumption",  [])                        
  trans _ = Nothing      

-- bewijs van Not p uit |- q en p |- Not q  
contradiction5 :: Rule (Context Env)
contradiction5 = liftToContext $ makeRule "contradiction5" trans
 where
  trans env@(Env ((as :|- F, inpr1):((bs :|- Not p), inpr2):gls) _ _) 
      | cond  = Just env
           { goals = [ (bs :|-  Not (Not p) :->: Not q, False)
                     , (bs :|- q :->: Not p, False)
                     ,((bs :|- Not p), inpr2)] <> gls
           }
    where         
      cond = not(null new)
      q = consequent (head new)
      new = [ t1
            | pl1 <- prooflines (availables env)
            , t1  <- maybeToList (term pl1)
            , pl2 <- prooflines (availables env)
            , t2  <- maybeToList (term pl2)
            , fits (consequent t1) (consequent t2)
            , let zs =  S.union (assumptions t1) (S.delete p (assumptions t2)), zs `S.isSubsetOf` bs 
            ]    
      fits p1 (Not p2) = p1 == p2
      fits _ _ = False         
  trans _ = Nothing        

  
-- bewijs van p uit Not p |- q,  Not p |- Not q  
contradiction6 :: Rule (Context Env)
contradiction6 = liftToContext $ makeRule "contradiction6" trans
 where
  trans env@(Env ((as :|- F, inpr1):((bs :|- p), inpr2):gls) _ _) 
      | cond  = Just env
           { 
            goals = [(bs :|- q :->:  p, False),(S.insert (Not p) bs :|- p, False),(bs :|- Not p :->:  p, False) ]++(goals env)
        --     goals = [ (bs :|- q :->:  p, False),(bs :|- Not p :->:  p, False)] ++ (goals env)
          --     goals = [ (bs :|- q :->:  p, False)] 
        --   goals = []
           , availables = (availables env) <> newav1 <> newav2
           }
    where         
      cond = not(null new)
      q = consequent (head new)
      newav1 = prooflineNr (nextNumber (availables env)) (axiomC p q)
                 ("Axiom c",  [])
      newav2 = prooflineNr (nextNumber (availables env)+ 1) (axiomA (Not q) (Not p))
                 ("Axiom a",  []) 
      new = [ t1
            | pl1 <- prooflines (availables env)
            , t1  <- maybeToList (term pl1)
            , pl2 <- prooflines (availables env)
            , t2  <- maybeToList (term pl2)
            , fits (consequent t1) (consequent t2)
            , let zs = S.delete (Not p)
                     $ S.union (assumptions t1) (assumptions t2), zs `S.isSubsetOf` bs  
            ]    
      fits p1 (Not p2) = p1 == p2 && not (p1 == (Not p)) && not (p == Not p1)
      fits _ _ = False         
  trans _ = Nothing         

     
-- bewijs van Not p uit p |- q,  p |- Not q  
contradiction7 :: Rule (Context Env)
contradiction7 = liftToContext $ makeRule "contradiction7" trans
 where
  trans env@(Env ((as :|- F, inpr1):((bs :|- Not p), inpr2):gls) _ _) 
      | cond  = Just env
           {  goals = [ ((S.insert (Not (Not p)) bs) :|-  q, False),((S.insert (Not (Not p)) bs) :|- Not q, False), 
                       ((bs :|- q :->: Not p), False), (as :|- F, inpr1),((bs :|- Not p), inpr2)  ] 
          --   goals = []
           , availables = availables env <> newav
           }
    where         
      cond = not(null new)
      q = consequent (head new)
      new = [ t1
            | pl1 <- prooflines (availables env)
            , t1  <- maybeToList (term pl1)
            , pl2 <- prooflines (availables env)
            , t2  <- maybeToList (term pl2)
            , fits (consequent t1) (consequent t2)
            , let zs = S.delete (p)
                     $ S.union (assumptions t1) (assumptions t2), zs `S.isSubsetOf` bs  
            ]    
      fits p1 (Not p2) = p1 == p2
      fits _ _ = False   
      newav = prooflineNr (nextNumber (availables env)) (S.singleton (Not (Not p)) :|- Not (Not p)) 
                 ("Assumption",  [])
  trans _ = Nothing      

axiomBheuristic1 :: Rule (Context Env)
axiomBheuristic1 = liftToContext $ makeRule "axiomBheuristic1" trans
 where
    trans env@(Env ((as :|- (p1 :->: q) :->: (p2 :->: r), _):gls) _ _) 
     | p1 == p2 && cond   = Just env
                { 
                 availables = availables env <> newav 
                }
     where               
      newav = prooflineNr (nextNumber (availables env)) (axiomB p1 q r)
                 ("Axiom b",  [])
      cond = any (== (p1 :->: (q :->: r)))[ consequent st
                                                                                              | pl <- prooflines (availables env)
                                                                                              , st <- maybeToList (term pl)
                                                                                              , S.isSubsetOf (assumptions st) as]
    trans _ = Nothing    
    
-- geprobeerd om de heuristiek na deductiestelling toe te laten passen (dus op tweede ipv eerste goal), maar dat geeft problemen met goal reached
axiomBheuristic2 :: Rule (Context Env)
axiomBheuristic2 = liftToContext $ makeRule "axiomBheuristic2" trans
 where
    trans env@(Env ((as :|- (p2 :->: r2), _):gls) _ _) 
     | cond   = Just env
                { 
                 availables = availables env <> newav1 <> newav2 
                }
     where               
      newav1 = prooflineNr (nextNumber (availables env)) newB ("Axiom b",  [])        
      
      newav2 = prooflineNr (nextNumber (availables env) + 1) newA ("Axiom a",  [])        
      cond = not (null $ catMaybes qList) 
              &&  ((findInProof newB (availables env)) == Nothing)
        --     &&  ((findInProofBy (superStatement (as:|- (head $ catMaybes qList))) (availables env))/= Nothing)
      qList = [ qFromCons $ consequent st
                                                                              | pl <- prooflines (availables env)
                                                                          , st <- maybeToList (term pl)
                                                                              , S.isSubsetOf (assumptions st) as
                                                                              ]
      qFromCons (p1 :->: (q :->: r1)) | p1 == p2 && r1 == r2 = Just q
      qFromCons _ = Nothing
      
      newB =  (axiomB p2 (head $ catMaybes qList) r2)
      newA = (axiomA  (head $ catMaybes qList) p2)
    trans _ = Nothing 
  

    
axiomCheuristic1 :: Rule (Context Env)
axiomCheuristic1 = liftToContext $ makeRule "axiomCheuristic1" trans
 where
    trans env@(Env ((as :|- p :->: q, _):gls) _ _) 
     | cond   = Just env
                { 
                 availables = availables env <> newav 
                }
     where               
      newav = prooflineNr (nextNumber (availables env)) (axiomC q p)
                 ("Axiom c",  [])        
      cond = any (== ((Not q) :->:(Not p)))[ consequent st
                                           | pl <- prooflines (availables env)
                                           , st <- maybeToList (term pl)
                                           , S.isSubsetOf (assumptions st) as]
    trans _ = Nothing    
    
axiomCheuristic2 :: Rule (Context Env)
axiomCheuristic2 = liftToContext $ makeRule "axiomCheuristic2" trans
 where
    trans env@(Env ((as :|- p :->: q,inpr):gls) _ _) 
     | cond   = Just env
                {
                 availables =  (availables env) <>  newav1 <>newav2 
                }
     where               
      newav1 = prooflineNr (nextNumber (availables env)) (axiomC q p)
                 ("Axiom c",  [])
      newav2 = prooflineNr (nextNumber (availables env)+ 1) (axiomA (Not p) (Not q))
                 ("Axiom a",  []) 
      cond = any (== (Not p))[ consequent st
                             | pl <- prooflines (availables env)
                             , st <- maybeToList (term pl)]
    trans _ = Nothing    
    
axiomCheuristic3 :: Rule (Context Env)
axiomCheuristic3 = liftToContext $ makeRule "axiomCheuristic3" trans
 where
    trans env@(Env ((as :|- p :->: q, inpr):gls) _ _) 
     | cond   = Just env
                {
                 availables =  (availables env) <>  newav1 <> newav2 <> newav3
                }
     where     
       cond   = not(null new)    
       new    = [ st
                | pl <- prooflines (availables env)
                , st  <- maybeToList (term pl)
                , consequent st == Not p
                , (Not q) `S.member` (assumptions st) 
                ]   
       newav1 = prooflineNr (nextNumber (availables env)) (axiomC q p)
                 ("Axiom c",  [])
       newav2 = prooflineNr (nextNumber (availables env)) (axiomA (Not p) (Not q))
                 ("Axiom a",  []) 
       newav3 = prooflineNr (nextNumber (availables env)) ((S.delete (Not q) (assumptions (head new))) :|- Not q :->: Not p)
                 ("Deduction", [42])           
    trans _ = Nothing   
    
skipFalse :: Rule (Context Env)
skipFalse = liftToContext $ makeRule "skipFalse" trans
 where
  trans env@(Env ((as :|- F, _):(st, inpr):gls) _ _) 
      | cond  = Just env
           {goals = (st, inpr):gls 
           }
         where         
         cond =  any ( `subStatement` st )[fromJust (term pl)| pl <- prooflines (availables env)]
 
  trans _ = Nothing       
    
    
useImplAssumption :: Rule (Context Env)
useImplAssumption = liftToContext $ minorRule "impl-assumption" trans
 where
   trans env = rec (filter isAssumption (mapMaybe term (prooflines (availables env))))
    where
      rec [] = Nothing
      rec ((_bs :|- p :->: _q):_) | notUsed (as :|- p) = Just env
         { goals = (as :|- p, False) : goals env
         }
      rec (_:rest) = rec rest
      
      as = case goals env of
              []        -> S.empty
              (bs :|- _, _):_ -> bs
    
      notUsed st = all f (goals env) && all g (mapMaybe term (prooflines (availables env)))
       where
         f (goal, _) = not (goal `subStatement` st)
         g a  = not (a `subStatement` st)
    
      isAssumption (qs :|- p) = p `S.member` qs
      
useNegAssumption :: Rule (Context Env)
useNegAssumption = liftToContext $ minorRule "neg-assumption" trans
 where
   trans env = rec (filter isAssumption (mapMaybe term (prooflines (availables env))))
    where
      rec [] = Nothing
      rec ((_bs :|- Not p):_) | notUsed (as :|- p) = Just env
         { goals = (as :|- p, False) : goals env
         }
      rec (_:rest) = rec rest
      
      as = case goals env of
              []        -> S.empty
              (bs :|- _, _):_ -> bs
    
      notUsed st = all f (goals env) && all g (mapMaybe term (prooflines (availables env)))
       where
         f (goal, _) = not (goal `subStatement` st)
         g a  = not (a `subStatement` st)
    
      isAssumption (qs :|- p) = p `S.member` qs
      
      
initProof :: Proof a -> Proof a
initProof = makeProof . initSafe . prooflines
 where
   initSafe xs = if null xs then [] else init xs
   
groundedProof :: Proof a -> Proof a
groundedProof = makeProof . takeWhile (motivated) . prooflines
  where
    motivated pl = not (null (label pl)) 
    
unGroundedProof :: Proof a -> Proof a
unGroundedProof = makeProof . dropWhile (motivated) . prooflines
  where
    motivated pl = not (null (label pl)) 
    
splitGroundedUngrounded :: Proof a -> (Proof a, Proof a)
splitGroundedUngrounded  p = (groundedProof p ,unGroundedProof p)

noSubstatementInProof :: Proof Statement ->  Statement -> Bool
noSubstatementInProof p x = 
   all (maybe False (nosuperStatement x) .term ) (prooflines p)
   
nosuperStatement :: Statement-> Statement -> Bool
nosuperStatement x y = not (subStatement y x)

superStatement :: Statement-> Statement -> Bool
superStatement x y =  subStatement y x

headTailProof :: Proof a -> (Proofline a, Proof a)
headTailProof p = let x:xs = prooflines p in (x, makeProof xs)

substatementInProof :: Statement ->  Proof Statement -> Bool
substatementInProof x p = 
   any (maybe False (superStatement x) .term ) (prooflines p)
--      any (maybe False (subStatement x) .term ) (prooflines p)
{-
goalAvailable :: [(Statement, Bool)] -> Proof Statement -> Bool
goalAvailable    [] avail = False
goalAvailable  ((x, inpr):xs) avail = substatementInProof x avail
-}

-- nu moet goalAvailable herhaald aangeroepen worden als het available goal dieper weg zit, dit is niet fraai maar werkt wel.
goalAvailable :: Rule (Context Env)
goalAvailable = liftToContext $ makeRule "goalAvailable" trans
 where
  trans env@(Env gls avail _)  
    |goalIsAvailable gls avail = Just env {goals = rec gls}
       where
       rec [] = []
       rec [a] = [a]
  --     rec (a:(x,inpr):gls1) | substatementInProof x avail = []
       rec (a:(x,inpr):gls1) | substatementInProof x avail = (x,inpr):gls1
       rec (a:(x,inpr):gls1) | otherwise = a : rec ((x,inpr):gls1)
  trans _ = Nothing   

deleteUnusedLines :: Rule (Context Env)
deleteUnusedLines = liftToContext $ makeRule "delete-unused-lines" trans
  where
    trans env@(Env _ _ prf)   |(unUsedlines prf) = Just env{proof = newproof prf}                              
                              | otherwise   = Nothing
    newproof prf  = makeProof  $ (filter (isUsed prf)(init $ prooflines prf)) ++ [last $ prooflines prf] 
    isUsed  prf x =  any (== fromJust (number x) )(concat $  map references (prooflines prf))
    isNotUsed prf x = not( any ( == fromJust (number x))(concat $  map references (prooflines prf)))
    unUsedlines prf = any  (isNotUsed prf) (init $ prooflines prf)

goalIsAvailable :: [(Statement, Bool)] -> Proof Statement -> Bool
goalIsAvailable    [] avail = False
goalIsAvailable    [(a, inpr)] avail = False
goalIsAvailable    ((a, True):xs) avail = False
goalIsAvailable  ((a, False):(x, inpr):xs) avail = substatementInProof x avail || goalIsAvailable ((x, inpr):xs) avail