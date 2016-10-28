module Domain.Logic.Axiomatic.ProofGeneratorDAG where

import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S
import Ideas.Common.Library
import qualified Ideas.Common.Library as Library
import Domain.Logic.Formula
import Domain.Logic.ProofDAG
import Domain.Logic.Axiomatic.Statement
import Domain.Logic.Axiomatic.Examples
import Domain.Logic.Axiomatic.Rules

axiomaticDagExercise :: Exercise Env
axiomaticDagExercise = emptyExercise
   { exerciseId     = describe "Axiomatic proofs" $ 
                      newId "logic.propositional.axiomatic.dag"
   , status         = Experimental
   , prettyPrinter  = show
   , strategy       = Library.label "axiomatic" (liftToContext axiomaticStrategy)
   , examples       = [ (dif, makeEnv a) | (dif, a) <- exampleList ]
   }    
   
axiomaticStrategy :: Strategy Env
axiomaticStrategy = 
   untilS stop
      $  goalAvailable
      |> implicationIntro
      |> elimGoal
   --   |> axiomBheuristic1 .*. repeatS modusPonens
   --   |> axiomBheuristic2 
      |> axiomCheuristic1 .*. repeatS modusPonens
      |> axiomCheuristic3 .*. repeatS modusPonens
      |> axiomCheuristic2 .*. repeatS modusPonens
      |> modusPonens
      |> doubleNegation
      |> deduction
      |> falseAsGoal
      |> negAsGoal 
      |> skipFalse
      |> contradiction1S
      |> contradiction1a .*. deduction -- .*. contradiction1S
      |> contradiction2S
      |> contradiction3 
      |> contradiction4
      |> contradiction5
      |> contradiction6 .*. repeatS modusPonens |> deduction
      |> contradiction7
      -- |> contradiction
      |> useImplAssumption
      |> useNegAssumption
 where
   stop = null . goals

-----------------------------------------------------------------
-- Sub-strategies

contradiction1S :: Strategy Env
contradiction1S =
   --   (contradiction1 .*. repeatS modusPonens .*. contradiction1seq .*. repeatS modusPonens |> implicationIntro |> elimGoal)
        contradiction1 .*. repeatS modusPonens .*. contradiction1seq .*. repeatS modusPonens

contradiction2S :: Strategy Env
contradiction2S = contradiction2 .*. contradiction2seq .*. repeatS modusPonens .*. contradiction1S


-----------------------------------------------------------------

data Axiomatic = Assumption | AxiomA | AxiomB | AxiomC | ModusPonens | Deduction
   deriving (Eq, Ord)
   
instance Show Axiomatic where
   show Assumption  = unqualified assumptionId
   show AxiomA      = unqualified axiomAId
   show AxiomB      = unqualified axiomBId
   show AxiomC      = unqualified axiomCId
   show ModusPonens = unqualified mpId
   show Deduction   = unqualified dedId

data Env = Env 
   { goals    :: [Statement]
   , proofDag :: ProofDag Axiomatic Statement
   }
   
statements :: Env -> [Statement]
statements = proofterms . proofDag

consequents :: Env -> [SLogic] 
consequents = map consequent . statements

---------------------------------------------

assumption :: SLogic -> ProofDag Axiomatic Statement
assumption p = [] ==> [p] |- p $ Assumption

axiomA2 :: SLogic -> SLogic -> ProofDag Axiomatic Statement
axiomA2 phi psi = [] ==> axiomA phi psi $ AxiomA

axiomB2 :: SLogic -> SLogic -> SLogic -> ProofDag Axiomatic Statement
axiomB2 phi psi chi = [] ==> axiomB phi psi chi $ AxiomB

axiomC2 :: SLogic -> SLogic -> ProofDag Axiomatic Statement
axiomC2 phi psi = [] ==> axiomC phi psi $ AxiomC

-- follows from deduction
axiomA :: SLogic -> SLogic -> Statement
axiomA phi psi = S.empty :|- phi :->: (psi :->: phi)

-- follows from deduction
axiomB :: SLogic -> SLogic -> SLogic -> Statement
axiomB phi psi chi = S.empty :|- (phi :->: (psi :->: chi)) :->: ((phi :->: psi) :->: (phi :->: chi))

axiomC :: SLogic -> SLogic -> Statement
axiomC phi psi = S.empty :|- (Not phi :->: Not psi) :->: (psi :->: phi)

---------------------------------------------

makeEnv :: Statement -> Env
makeEnv st@(ps :|- _) = Env 
   { goals     = [st]
   , proofDag  = mconcat [ assumption p | p <- S.toList ps ]
   }
    
instance Show Env where
   show env = intercalate "\n"
      [ column "goals"  $ map show (goals env)
      , column "proofDag" $ lines (show (proofDag env))
      ]
    where
      column s xs = intercalate "\n" $ (s ++ ":") : map ("  " ++) xs
 
mmsee :: Int -> IO ()
mmsee i = printDerivation axiomaticDagExercise (makeEnv $ snd $ mmExampleList !! i)

see :: Int -> IO ()
see i = printDerivation axiomaticDagExercise (makeEnv $ snd $ exampleList !! i)

modusPonens :: Rule Env
modusPonens = makeRule "modus-ponens" trans
 where
   trans env
      | null fs   = Nothing
      | otherwise = env { proofDag = proofDag env <> new } `extends` env
    where
      new = mconcat fs
      fs  = [ [a, b] ==> st $ ModusPonens
            | a <- statements env
            , b <- statements env
            , st  <- isMP a b
            -- , all (\x -> not (x `subStatement` st)) (statements env)
            ]
                       
      isMP (as1 :|- p1 :->: q) (as2 :|- p2) | p1 == p2 =
         [ as1 `S.union` as2 :|- q ]
      isMP _ _ = []

extends :: Env -> Env -> Maybe Env
extends new old 
   | proofDag new == proofDag old = Nothing
   | otherwise  = Just new

doubleNegation :: Rule Env
doubleNegation = makeRule "double-negation" trans
 where
   trans env 
      | null fs   = Nothing
      | otherwise = env { proofDag = proofDag env <> mconcat (take 3 new) } -- waarom is take 3 hier nodig?
           `extends` env
    where
      new = mconcat fs
      fs  =  [ [ axiomA2 con (Not (Not con)) 
               , axiomC2 (Not con) (Not pcon)
               , axiomC2 pcon con
               ]
            | st <- statements env
            , let con = consequent st
            , pcon <- isDoubleNeg con
           -- , all (\x -> not (x `subStatement` (assumptions st :|- pcon)))
           --       (statements env)
            ] 
            
      isDoubleNeg (Not (Not p)) = [p]
      isDoubleNeg _ = []

-- voegt een implicatie (via deductiestelling) toe aan de proofDag, en 
-- verwijdert de bijbehorende doelen
implicationIntro :: Rule Env
implicationIntro = makeRule "impl-intro" trans
 where
   trans env@(Env (csr:(_ :|- p :->: q):gls) _) 
      | not newIsEmpty = Just env
           { goals = gls
           , proofDag = proofDag env <> new
           }
    where
      qs  = [ [a] ==> S.delete p as1 :|- p :->: q1 $ Deduction
            | a <- statements env
            , let as1 :|- q1 = a
            , q1 == q
            , (as1 :|- q1) `subStatement` csr 
            ]
   
      new = mconcat qs
      newIsEmpty = null $ proofterms new

   trans _ = Nothing

-- bewijs een doel mbv deductiestelling: voeg doel toe en voeg regels  toe aan 
-- het bewijs, als die er niet al in staan
deduction :: Rule Env
deduction = makeRule "deduction" trans
 where
   trans env@(Env ((st@(as :|- p :->: q)):gls) _) = Just
      env { goals = newst:st:gls
          , proofDag = proofDag env <> avp
          }
    where
      avp   = assumption p
      newst = addAssumption p (as :|- q)
   trans _ = Nothing

   
 --       grounded = groundedProof (proof env) 
  --    ungrounded = unGroundedProof (proof env)
-- doel bereikt: voeg motivatie toe als regel al in het bewijs staat, voeg 
-- anders regel + motivatie toe
elimGoal :: Rule Env
elimGoal = makeRule "elim-goal" trans
 where
   trans env@(Env ((as :|- p):gls) _)
      |  reached = Just env { goals = gls }
    where
      reached =
         let ok2 (bs :|- q) = p == q && bs `S.isSubsetOf` as
         in any ok2 (statements env)
   trans _ = Nothing
   
falseAsGoal :: Rule Env
falseAsGoal = makeRule "false-goal" trans
 where
   trans env@(Env ((as :|- p@(Var _)):_) _) 
      | p /= F = Just env
           { goals = addAssumption (Not p) (as :|- F) : goals env
           , proofDag = proofDag env <> new
           }
    where
      new = assumption (Not p)
   trans _ = Nothing

negAsGoal :: Rule Env
negAsGoal = makeRule "neg-goal" trans
 where
   trans env@(Env ((as :|- Not p):(_ :|- q):_) _) | q/= F = Just env
      { goals = addAssumption p (as :|- F) : goals env 
      , proofDag = proofDag env <> new
      }
      where
       new = assumption p
   trans env@(Env ((as :|- Not p):_) _)  = Just env
      {goals = addAssumption p (as :|- F) : goals env 
      , proofDag = proofDag env <> new
      } 
     where
       new = assumption p
   trans _ = Nothing

-- hulpstelling: bewijs dmv contradictie; als de tebewijzen formule al in het 
-- bewijs staat, voegt contradiction voor deze regel de contradictie toe, anders 
-- wordt boven aan het bewijs contradictie + conclusie toegevoegd
{-
contradiction :: Rule Env
contradiction = makeRule "contradiction" trans
 where
   trans env@(Env ((_ :|- F):(bs :|- p):gls) _)
      | cond = Just env
           { goals = gls 
           , proofDag = proofDag env <> newav
           }
    where
      cond   = not (null new)
      newav  = head new
   
      new = [ [t1, t2] ==> zs :|- p $ "Contradiction"
            | t1 <- statements env
            , t2 <- statements env
            , fits (consequent t1) (consequent t2)
            , let zs = S.delete (neg p)
                     $ S.union (assumptions t1) (assumptions t2), zs `S.isSubsetOf` bs 
            ]
  
      fits p1 (Not p2) = p1 == p2
      fits _ _ = False 
      
      neg (Not x) = x
      neg x       = Not x

   trans _ = Nothing
-}

--   bewijs van p uit Not p -> p
contradiction1 :: Rule Env
contradiction1 = makeRule "contradiction1" trans
 where
  trans env@(Env ((as :|- F):(st2@(_ :|- p)):gls) _) 
      | cond  = Just env
           { goals = st2:gls  
           , proofDag = proofDag env <> mconcat newav
           }
    where         
       cond = (Not p :->: p) `elem` 
          [ consequent st
          | st <- statements env
          , S.isSubsetOf (assumptions st) as 
          ]  
       newav = [ axiomA2 (Not p) (Not (Not (Not p :->: p))) 
               , axiomC2 (Not (Not p :->: p)) p
               , axiomC2 p (Not p :->: p)
               , axiomB2 (Not p) p (Not (Not p :->: p))
               ]      
  trans _ = Nothing    

 -- bewijs van |- Not p -> p uit Not p |- p
contradiction1a :: Rule Env
contradiction1a = makeRule "contradiction1a" trans
 where
  trans env@(Env ((as :|- F):(cs :|- p):_) _) 
      | cond  = Just env
           { goals = (cs:|- Not p :->: p) : goals env
           }
    where         
      cond = any ok (statements env)
      ok (bs :|- q) = q == p && bs `S.isSubsetOf` as  && Not p `S.member` bs

  trans _ = Nothing      
  
contradiction1seq :: Rule Env
contradiction1seq = makeRule "contradiction1seq" trans
 where
  trans env@(Env((st@(_ :|- p)):gls) _) 
          = Just env
           { goals = st:gls
           , proofDag = proofDag env <> head newav
           }
    where         
        newav = [ [t] ==> S.empty :|- Not p :->: p :->: Not (Not p :->: p) $ Deduction
                | t <- statements env
                , let as1 :|- q1 = t
                , q1 == (p :->: Not (Not p :->: p)) && as1 == S.singleton (Not p)
                ]
  trans _ = Nothing 
  
--  Bewijs van p uit Not p -> Not Not p 
contradiction2 :: Rule Env
contradiction2 = makeRule "contradiction2" trans
 where
  trans env@(Env ((_ :|- F):(_ :|- p):_) _) 
      | cond  = Just env
           {  
           proofDag = proofDag env <> newav
           }
    where         
       cond = (Not  p :->: Not (Not p)) `elem` consequents env
       newav = assumption (Not (Not p))
              
  trans _ = Nothing    
                     
contradiction2seq :: Rule Env
contradiction2seq = makeRule "contradiction2seq" trans
 where
  trans env@(Env ((_ :|- F):(_ :|- p):_) _) 
      | cond  = Just env
           { proofDag = proofDag env <> newav
           }
    where         
       cond = (Not  p :->: Not (Not p)) `elem` consequents env
       newav = axiomC2 p (Not p)
              
  trans _ = Nothing    

-- bewijs van Not p uit p -> Not p  
contradiction3 :: Rule Env
contradiction3 = makeRule "contradiction3" trans
 where
  trans env@(Env ((as :|- F):(bs :|- Not p):_) _) 
      | cond  = Just env
           {goals = [ bs :|- Not (Not p) :->: Not p, as :|- F, bs :|- Not p ] 
           }
    where         
       cond = (p :->: Not p) `elem` consequents env
  trans _ = Nothing      


-- bewijs van Not p uit p |- q en |- Not q  
contradiction4 :: Rule Env
contradiction4 = makeRule "contradiction4" trans
 where
  trans env@(Env ((as :|- F):(bs :|- Not p):gls) _) 
      | cond1 = Just env
           { goals = [ bs :|- Not (Not p) :->: Not (Not q)
                     , bs :|- Not q :->: Not p
                     , bs :|- Not p 
                     ] ++ gls
           , proofDag = proofDag env <> newav1 
           }
      | cond  = Just env
           { goals = [ S.union bs (S.singleton (Not (Not p))) :|- q
                     , S.empty  :|- Not(Not (Not q)) :->: Not q
                     , as :|- F
                     , bs :|- Not p
                     ] <> gls
                    
           , proofDag = proofDag env <> newav 
           }
    where         
      cond1 = cond && ([] |- Not(Not (Not q)) :->: Not q) `elem` statements env
      cond = not(null new)
      q = head new
      new = [ consequent t1
            | t1 <- statements env
            , t2 <- statements env
            , fits (consequent t1) (consequent t2)
            , let zs =  S.union (S.delete p (assumptions t1)) (assumptions t2)
            , zs `S.isSubsetOf` bs 
            ]
      newav1 = axiomC2 (Not(Not q)) q
      fits p1 (Not p2) = p1 == p2
      fits _ _ = False 
      newav = assumption (Not (Not p))                    
  trans _ = Nothing      

-- bewijs van Not p uit |- q en p |- Not q  
contradiction5 :: Rule Env
contradiction5 = makeRule "contradiction5" trans
 where
  trans env@(Env ((_ :|- F):(bs :|- Not p):gls) _) 
      | cond  = Just env
           { goals = [ bs :|-  Not (Not p) :->: Not q
                     , bs :|- q :->: Not p
                     , bs :|- Not p
                     ] <> gls
           }
    where         
      cond = not(null new)
      q = head new
      new = [ consequent t1
            | t1 <- statements env
            , t2 <- statements env
            , fits (consequent t1) (consequent t2)
            , let zs =  S.union (assumptions t1) (S.delete p (assumptions t2))
            , zs `S.isSubsetOf` bs 
            ]    
      fits p1 (Not p2) = p1 == p2
      fits _ _ = False         
  trans _ = Nothing        

  
-- bewijs van p uit Not p |- q,  Not p |- Not q  
contradiction6 :: Rule Env
contradiction6 = makeRule "contradiction6" trans
 where
  trans env@(Env ((_ :|- F):(bs :|- p):_) _) 
      | cond  = Just env
           { goals = [ bs :|- q :->:  p
                     , S.insert (Not p) bs :|- p
                     , bs :|- Not p :->:  p 
                     ] ++ goals env
           , proofDag = proofDag env <> newav1 <> newav2
           }
    where         
      cond = not(null new)
      q = head new
      newav1 = axiomC2 p q
      newav2 = axiomA2 (Not q) (Not p)
      new = [ consequent t1
            | t1 <- statements env
            , t2 <- statements env
            , fits (consequent t1) (consequent t2)
            , let zs = S.delete (Not p)
                     $ S.union (assumptions t1) (assumptions t2)
            , zs `S.isSubsetOf` bs  
            ]    
      fits p1 (Not p2) = p1 == p2 && p1 /= Not p && p /= Not p1
      fits _ _ = False         
  trans _ = Nothing         

     
-- bewijs van Not p uit p |- q,  p |- Not q  
contradiction7 :: Rule Env
contradiction7 = makeRule "contradiction7" trans
 where
  trans env@(Env ((as :|- F):(bs :|- Not p):_) _) 
      | cond  = Just env
           {  goals = [ S.insert (Not (Not p)) bs :|-  q
                      , S.insert (Not (Not p)) bs :|- Not q
                      , bs :|- q :->: Not p
                      , as :|- F
                      , bs :|- Not p  
                      ] 
           , proofDag = proofDag env <> newav
           }
    where         
      cond = not(null new)
      q = head new
      new = [ consequent t1
            | t1 <- statements env
            , t2 <- statements env
            , fits (consequent t1) (consequent t2)
            , let zs = S.delete p $ S.union (assumptions t1) (assumptions t2)
            , zs `S.isSubsetOf` bs  
            ]    
      fits p1 (Not p2) = p1 == p2
      fits _ _ = False   
      newav = assumption (Not (Not p))
  trans _ = Nothing      

axiomBheuristic1 :: Rule Env
axiomBheuristic1 = makeRule "axiomBheuristic1" trans
 where
    trans env@(Env ((as :|- (p1 :->: q) :->: (p2 :->: r)):_) _) 
     | p1 == p2 && cond   = Just env
                { 
                 proofDag = proofDag env <> newav 
                }
     where               
      newav = axiomB2 p1 q r
      cond = (p1 :->: (q :->: r)) `elem`
         [ consequent st
         | st <- statements env
         , S.isSubsetOf (assumptions st) as
         ]
    trans _ = Nothing    
    
-- geprobeerd om de heuristiek na deductiestelling toe te laten passen (dus op tweede ipv eerste goal), maar dat geeft problemen met goal reached
axiomBheuristic2 :: Rule Env
axiomBheuristic2 = makeRule "axiomBheuristic2" trans
 where
    trans env@(Env ((as :|- (p2 :->: r2)):_) _)
     | cond   = Just env
                { 
                 proofDag = proofDag env <> newav1 <> newav2 
                }
     where               
      newav1 = axiomB2 p2 (head qList) r2
      newav2 = axiomA2 (head qList) p2
      cond = not (null qList) 
              &&  (head (proofterms newav1) `notElem` statements env)
      qList = catMaybes 
                 [ qFromCons (consequent st)
                 | st <- statements env
                 , S.isSubsetOf (assumptions st) as
                 ]
      qFromCons (p1 :->: (q :->: r1)) | p1 == p2 && r1 == r2 = Just q
      qFromCons _ = Nothing

    trans _ = Nothing 
  

    
axiomCheuristic1 :: Rule Env
axiomCheuristic1 = makeRule "axiomCheuristic1" trans
 where
    trans env@(Env ((as :|- p :->: q):_) _)
     | cond   = Just env
                { 
                 proofDag = proofDag env <> newav 
                }
     where               
      newav = axiomC2 q p      
      cond = (Not q :->: Not p) `elem` 
         [ consequent st
         | st <- statements env
         , S.isSubsetOf (assumptions st) as
         ]
    trans _ = Nothing    
    
axiomCheuristic2 :: Rule Env
axiomCheuristic2 = makeRule "axiomCheuristic2" trans
 where
    trans env@(Env ((_ :|- p :->: q):_) _) 
     | cond   = Just env
                {
                 proofDag = proofDag env <> newav1 <> newav2 
                }
     where               
      newav1 = axiomC2 q p
      newav2 = axiomA2 (Not p) (Not q)
      cond = Not p `elem` consequents env

    trans _ = Nothing    
    
axiomCheuristic3 :: Rule Env
axiomCheuristic3 = makeRule "axiomCheuristic3" trans
 where
    trans env@(Env ((_ :|- p :->: q):_) _) 
     | cond   = Just env
                {
                 proofDag = proofDag env <>  newav1 <> newav2 <> newav3
                }
     where     
       cond   = not (null new)    
       new    = [ assumptions st
                | st <- statements env
                , consequent st == Not p
                , Not q `S.member` assumptions st
                ]   
       newav1 = axiomC2 q p
       newav2 = axiomA2 (Not p) (Not q)
       newav3 = [] ==> S.delete (Not q) (head new) :|- Not q :->: Not p $ Deduction
    trans _ = Nothing   
    
skipFalse :: Rule Env
skipFalse = makeRule "skipFalse" trans
 where
  trans env@(Env ((_ :|- F):st:gls) _) 
      | cond  = Just env { goals = st:gls }
         where         
         cond =  any ( `subStatement` st) (statements env)
 
  trans _ = Nothing       
    
    
useImplAssumption :: Rule Env
useImplAssumption = minorRule "impl-assumption" trans
 where
   trans env = rec (filter isAssumption (statements env))
    where
      rec [] = Nothing
      rec ((_bs :|- p :->: _q):_) | notUsed (as :|- p) env = Just env
         { goals = (as :|- p) : goals env
         }
      rec (_:rest) = rec rest
      
      as = case goals env of
              []        -> S.empty
              (bs :|- _):_ -> bs
    
notUsed :: Statement -> Env -> Bool
notUsed st env = all f (goals env) && all g (statements env)
   where
      f goal = not (goal `subStatement` st)
      g a    = not (a `subStatement` st)
    
isAssumption :: Statement -> Bool
isAssumption (qs :|- p) = p `S.member` qs
      
useNegAssumption :: Rule Env
useNegAssumption = minorRule "neg-assumption" trans
 where
   trans env = rec (filter isAssumption (statements env))
    where
      rec [] = Nothing
      rec ((_bs :|- Not p):_) | notUsed (as :|- p) env = Just env
         { goals = (as :|- p) : goals env
         }
      rec (_:rest) = rec rest
      
      as = case goals env of
              []           -> S.empty
              (bs :|- _):_ -> bs

substatementInProof :: Statement -> ProofDag Axiomatic Statement -> Bool
substatementInProof x p = 
   any (`subStatement` x) (proofterms p)

-- nu moet goalAvailable herhaald aangeroepen worden als het available goal dieper weg zit, dit is niet fraai maar werkt wel.
goalAvailable :: Rule Env
goalAvailable = makeRule "goalAvailable" trans
 where
  trans env@(Env gls avail)  
    | goalIsAvailable gls avail = Just env {goals = rec gls}
       where
       rec [] = []
       rec [a] = [a]
       rec (a:x:gls1) 
          | substatementInProof x avail = x:gls1 
          | otherwise = a : rec (x:gls1)
  trans _ = Nothing   

goalIsAvailable :: [Statement] -> ProofDag Axiomatic Statement -> Bool
goalIsAvailable [] _  = False
goalIsAvailable [_] _ = False
goalIsAvailable  (_:x:xs) avail = substatementInProof x avail || goalIsAvailable (x:xs) avail