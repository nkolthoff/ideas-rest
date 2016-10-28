module Domain.Logic.Axiomatic.Exercise (logaxExercise) where

import Data.Char
import Data.Function
import Data.Maybe
import Domain.Logic.Formula
import Domain.Logic.Parser
import Domain.Logic.LinearProof
import Domain.Logic.Axiomatic.Statement
import Domain.Logic.Axiomatic.Examples
import Domain.Logic.Axiomatic.Rules
import Domain.Logic.Axiomatic.BuggyRules
import Domain.Logic.ProofDAG (strategyGenerator, makeGoal)
import Domain.Logic.Axiomatic.ProofGeneratorDAG (axiomaticStrategy, Env(..), makeEnv)
import Ideas.Common.Library hiding (label, lastTerm)
import Ideas.Encoding.Encoder
import qualified Data.Set as S
import qualified Ideas.Common.Library as Ideas

logaxExercise :: Exercise (Proof Statement)
logaxExercise = latexEncoding $ jsonEncoding emptyExercise
   { exerciseId     = describe "Axiomatic proofs" $ 
                      newId "logic.propositional.logax"
   , status         = Experimental
   , prettyPrinter  = show
   , parser         = parseProof
   , suitable       = predicate partialProof
   , ready          = predicate proofIsReady
   , equivalence    = withoutContext equalProof
   , similarity     = withoutContext similarProof
   , hasTermView    = Just termView
   , strategy       = Ideas.label "logic.propositional.logax" (liftToContext logaxStrategy)
   , extraRules     = map liftToContext $
                         [ assumptionR
                         , axiomAR, axiomBR, axiomCR
                         , mpForwardR, mpMiddle1R, mpMiddle2R, mpCloseR
                         , dedForwardR, dedBackwardR, dedCloseR
                         , goalR, renumberR
                         ] ++ buggyRules 
   , examples       = [ (dif, p) 
                      | (dif, st) <- exampleList ++ mmExampleList
                      , p <- maybeToList (createGoal st mempty)
                      ]
   }

logaxStrategy :: Strategy (Proof Statement)
logaxStrategy = dynamic "logic.propositional.logax.generator" logaxStrategyGen

logaxStrategyGen :: Proof Statement -> Strategy (Proof Statement)
logaxStrategyGen p = strategyGenerator dag
 where
   goal = fromJust $ term $ last $ prooflines p
   env  = makeEnv goal
   dag = proofDag (applyD axiomaticStrategy env) <> makeGoal goal

parseProof :: String -> Either String (Proof Statement)
parseProof s = 
   case rights (map parseProofline (filter (any (not . isSpace)) (lines s))) of
      Left err -> Left err
      Right xs -> Right (makeProof (concatMap prooflines xs))
 where
   rights :: [Either a b] -> Either a [b]
   rights [] = Right []
   rights (Left s:_) = Left s
   rights (Right a:xs) = either Left (Right . (a:)) (rights xs)


parseProofline :: String -> Either String (Proof Statement)
parseProofline s = 
   case span isDigit (dropWhile isSpace s) of 
      (nr, '.':s1) | not (null nr) -> 
         let (s2, s3) = break (== '[') s1 
         in case (parseStatement False s2, parseMotivation s3) of
               (Left err, _) -> Left err
               (_, Left err) -> Left err
               (Right (ps, q), Right mot) -> Right $ prooflineNr (read nr) (ps |- q) mot
      _ -> Left "not a proofline"

parseMotivation :: String -> Either String Motivation
parseMotivation s =
   case dropWhile isSpace s of
      "" -> Right ([], [])
      '[':s1 -> let (s2, s3) = break (`elem` ",]") s1
                    is = read ('[':dropWhile (==',') s3)
                in Right (s2, is)
      _ -> Left "not a motivation"

-- for now, we assume that the goal is in the last proof line
proofIsReady :: Proof Statement -> Bool
proofIsReady p = maybe False (`goalIsReached` p) (lastTerm p) && partialProof p

partialProof :: Proof Statement -> Bool
partialProof p = -- we negeren voorlopig de motivatie
   all validStatement (mapMaybe term (prooflines p))

goalIsReached :: Statement -> Proof Statement -> Bool
goalIsReached goal p = 
   isJust (findInProof goal p) && all motivated (prooflines p)
 where
   motivated pl =
      case (number pl, term pl) of
         (Just i, Just _) -> not (null (label pl)) && all (< i) (references pl)
         _ -> False

lastTerm :: Proof a -> Maybe a
lastTerm p = listToMaybe (reverse (prooflines p)) >>= term

equalProof :: Proof Statement -> Proof Statement -> Bool
equalProof p1 p2 = fromMaybe False $ do
   t1 <- lastTerm p1 
   t2 <- lastTerm p2
   return $ t1 `similarStatement` t2 
      && partialProof p1 && partialProof p2

similarProof :: Proof Statement -> Proof Statement -> Bool
similarProof p1 p2 = and (zipWith similarProofline xs ys)
 where
   xs = prooflines (renumber p1)
   ys = prooflines (renumber p2)

similarProofline :: Proofline Statement -> Proofline Statement -> Bool
similarProofline pl1 pl2 = 
   checkTerm (term pl1) (term pl2) &&
   checkMotivation (motivation pl1) (motivation pl2)
 where
   checkTerm (Just t1) (Just t2) = similarStatement t1 t2
   checkTerm Nothing Nothing = True
   checkTerm _ _ = False
   
   checkMotivation (s, is) (t, js) =
      s == t && is == js

similarStatement :: Statement -> Statement -> Bool
similarStatement st1 st2 = 
   consequent st1 == consequent st2 && validStatement (xs :|- consequent st1)
 where
   -- door de intersectie nemen kun je assumpties introduceren waar je niet meer 
   -- vanaf komt. Eigenlijk zou hier op gecontroleerd moeten worden (in de 
   -- context van het bewijs).
   xs = assumptions st1 `S.intersection` assumptions st2

see n = printDerivation logaxExercise (fromJust (createGoal (snd (exampleList !! n)) mempty))