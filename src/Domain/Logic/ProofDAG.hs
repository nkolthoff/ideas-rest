module Domain.Logic.ProofDAG 
   ( ProofDag, (==>), proofterms
   , strategyGenerator, makeDag, makeGoal
   ) where

import Control.Monad
import Data.List (intercalate, (\\))
import Data.Maybe
import Domain.Logic.LinearProof hiding (Motivation, goal, label)
import Ideas.Common.Library
import qualified Domain.Logic.LinearProof as LP
import qualified Data.Map as M
import qualified Data.Set as S

infix 1 ==>

type Motivation l a = (l, [a])

data ProofDag l a = PD
   { nodeMap :: M.Map a (S.Set (Motivation l a))
   , goalSet :: S.Set a
   } 
 deriving Eq
   
instance (Show l, Ord a, Show a) => Show (ProofDag l a) where
   show dag = unlines $ 
      [ f a m | (a, ms) <- M.toList (nodeMap dag), m <- S.toList ms ]
      ++ ["\nGoals: " ++ intercalate ", " (map show (S.toList (goalSet dag)))]
    where
      f a (l, xs) = intercalate ", " (map show xs) ++ " ==> " ++ 
         show a ++ "   [" ++ show l ++ "]"
 
instance (Ord l, Ord a) => Monoid (ProofDag l a) where
   mempty = PD mempty mempty
   mappend (PD m1 g1) (PD m2 g2) = PD (M.unionWith (<>) m1 m2) (g1 <> g2)

makeGoal :: a -> ProofDag l a
makeGoal a = PD M.empty (S.singleton a)

makeGoals :: Ord a => [a] -> ProofDag l a
makeGoals as = PD M.empty (S.fromList as)

addTerms :: (Ord l, Ord a) => [a] -> ProofDag l a -> ProofDag l a
addTerms xs dag = PD (M.fromList [ (x, S.empty) | x <- xs ]) mempty <> dag

(==>) :: Ord a => [a] -> a -> l -> ProofDag l a
xs ==> y = \s -> PD (M.singleton y (S.singleton (s, xs))) mempty
 
goalTerms :: ProofDag l a -> [a]
goalTerms = S.toList . goalSet

proofterms :: Ord a => ProofDag l a -> [a]
proofterms = S.toList . prooftermSet

prooftermSet :: Ord a => ProofDag l a -> S.Set a
prooftermSet dag =
   let xs = concatMap (concatMap snd . S.toList) (M.elems (nodeMap dag))
   in goalSet dag <> M.keysSet (nodeMap dag) <> S.fromList xs
    
makeDag :: Ord a => [a] -> Proof a -> ProofDag String a
makeDag gls p = mconcat $ makeGoals gls : mapMaybe f (prooflines p)
 where
   f pl = do 
      a  <- term pl
      xs <- mapM find (references pl)
      return (xs ==> a $ LP.label pl)
      
   find i = findNumber i p >>= term

-- Een goal is een statement dat nog niet gemotiveerd is
--
-- 1) sluiten van een bewijs voor een goal
--    -> motivatie toevoegen
-- 2) achteruit stappen (deductie stelling altijd een goed idee, MP niet zo heel gauw)
--    -> motiveert goal, maakt een nieuw goal
-- 3) gebruiken van statements die er al zijn (voorwaartse stap, is bijna altijd MP en niet Ded)
--    -> ook hier, slim kijken of het wel nodig is
-- 4) introduceren van een assumptie/axioma (lage prioriteit), dat zijn de regels zonder afhankelijkheid
--    -> welke ga ik gebruiken? slim zijn!
--          (a) introduceer wat direct tot een vervolg combinatie stap leidt
--          (b) introduceer iets waarvoor nog een andere assumptie/axioma nodig is voor zo'n vervolgstap
--          (c) kies maar iets (maar dat komt niet voor...)

strategyGenerator :: (Ord a, Ord l, Show l) => ProofDag l a -> Strategy (Proof a)
strategyGenerator dag = untilS (null . getGoals) $
   choice [ closeStep    l i dag | (l, i) <- zip ls [0..] ] 
   |> (   choice [ backwardStep l i dag | (l, i) <- zip ls [0..] ]
      ./. choice [ forwardStep  l i dag | (l, i) <- zip ls [0..] ]
      ./. choice [ introStepDirect     dag l i | (l, i) <- zip ls [0..] ]
      ./. choice [ introStepTwos  twos dag l i | (l, i) <- zip ls [0..] ]     
      ./. choice [ introStep           dag l i | (l, i) <- zip ls [0..] ]
      )
 where
   ls = S.toList (S.unions (map (S.map fst) (M.elems (nodeMap dag))))
   
   leafs = M.keysSet (M.filter (any (null . snd) . S.toList) (nodeMap dag))
   twos  = M.keysSet (M.filter (any (isTwo . snd) . S.toList) (nodeMap dag))
    where
      isTwo xs = not (null xs) && all (`S.member` leafs) xs

closeStep :: (Ord a, Show l, Eq l) => l -> Int -> ProofDag l a -> Rule (Proof a)
closeStep l0 i dag = makeRule (show l0 # "close" # show i) $ \p -> do
   (goalnr, goal) <- getGoals p
   (l, as) <- maybe [] S.toList (M.lookup goal (nodeMap dag))
   guard (l == l0)
   is <- mapM (\a -> maybeToList (findInProof a p >>= number)) as
   guard (all (< goalnr) is)
   return $ addMotivation goalnr (show l, is) p

backwardStep :: (Ord a, Show l, Eq l) => l -> Int -> ProofDag l a -> Rule (Proof a)
backwardStep l0 i dag = makeRule (show l0 # "backward" # show i) $ \p -> do
   (goalnr, goal) <- getGoals p
   (l, as) <- maybe [] S.toList (M.lookup goal (nodeMap dag))
   guard (l == l0)
   guard (length as == 1)
   let (p1, p2) = splitProof p
       i = prevNumber p2
   return $ makeProof $ 
      prooflines p1 ++ 
      prooflines (goalNr i (head as)) ++
      prooflines (addMotivation goalnr (show l, [i]) p2)

forwardStep :: (Ord a, Show l, Eq l) => l -> Int -> ProofDag l a -> Rule (Proof a)
forwardStep l0 i dag = makeRule (show l0 # "forward" # show i) $ \p -> do
   (a, mots) <- M.toList (nodeMap dag)
   guard (not (has a p))
   (l, as)   <- S.toList mots
   guard (l == l0)
   guard (not (null as))
   let (p1, p2) = splitProof p 
       i = nextNumber p1
   is <- mapM (\a -> maybeToList (findInProof a p1 >>= number)) as
   return $ makeProof $
      prooflines p1 ++
      prooflines (prooflineNr i a (show l, is)) ++
      prooflines p2

introStepDirect :: (Ord a, Show l, Eq l) => ProofDag l a -> l -> Int -> Rule (Proof a)
introStepDirect dag = intro dag $ \a p -> 
   let directSet = any direct . S.toList
       direct (_, as) = a `elem` as && all (`has` p) (as \\ [a])
   in not (has a p) && any directSet (M.elems (nodeMap dag))
      
introStepTwos :: (Ord a, Show l, Eq l) => S.Set a -> ProofDag l a ->  l -> Int -> Rule (Proof a)
introStepTwos twos dag = intro dag $ \a p ->
   let twoSet (b, s) = any (isTwo b) (S.toList s)
       isTwo b (_, as) = a `elem` as && b `S.member` twos
   in not (has a p) && any twoSet (M.toList (nodeMap dag))
      
introStep :: (Ord a, Show l, Eq l) => ProofDag l a -> l -> Int -> Rule (Proof a)
introStep dag = intro dag $ \a p -> not (has a p)

intro :: (Ord a, Show l, Eq l) => ProofDag l a -> (a -> Proof a -> Bool) -> l -> Int -> Rule (Proof a)
intro dag condition l0 i = makeRule (show l0 # "intro" # show i) $ \p -> do
   (a, mots) <- M.toList (nodeMap dag)
   guard (condition a p) -- check the condition
   (l, as)   <- S.toList mots
   guard (l == l0)
   guard (null as)
   let (p1, p2) = splitProof p 
       i = nextNumber p1
   return $ makeProof $
      prooflines p1 ++
      prooflines (prooflineNr i a (show l, [])) ++
      prooflines p2

has :: Eq a => a -> Proof a -> Bool
has a p = a `elem` mapMaybe term (prooflines p)

prevNumber :: Proof a -> Int
prevNumber p = minimum (1001 : usedNumbers p) - 1

splitProof :: Proof a -> (Proof a, Proof a)
splitProof p = (makeProof xs, makeProof ys)
 where
    (xs, ys) = break unmotivated (prooflines p)
   
unmotivated :: Proofline a -> Bool
unmotivated = null . LP.label

getGoals :: Proof a -> [(Int, a)]
getGoals = mapMaybe f . filter unmotivated . prooflines
 where
   f pl = liftM2 (,) (number pl) (term pl)

depends :: Ord a => ProofDag l a -> a -> [S.Set a]
depends dag = rec 
 where
   rec a = [ S.insert a (S.unions xs)
           | (_, as) <- maybe [] S.toList (M.lookup a (nodeMap dag))
           , xs <- combi (map rec as)
           ]
           
combi :: [[a]] -> [[a]]
combi [] = [[]]
combi (xs:xss) = [ y:ys | y <- xs, ys <- combi xss ]

--------------------------------------------------------

exDag :: ProofDag String String
exDag = makeGoal "P" <> mconcat 
   [ ["Q","R"] ==> "P"   $ "MP"
   , ["S"]     ==> "Q"   $ "Ded"
   , ["X"]     ==> "R"   $ "Ded"
   , ["S"]     ==> "X"   $ "Ded"
   , ["T"]     ==> "X"   $ "Ded"
   , []        ==> "S"   $ "Axiom"
   , []        ==> "T"   $ "As"
   ] 

exDag1 :: ProofDag String String
exDag1 = makeGoal "R->Q" <> mconcat  
   [ []            ==> "P"    $ "As"
   , []            ==> "P->Q" $ "As"
   , ["P", "P->Q"] ==> "Q"    $ "MP"
   , ["Q"]         ==> "R->Q" $ "Ded"
   ]  

exDag2 :: ProofDag String String
exDag2 = makeGoal "R->P->Q" <> mconcat 
   [ []        ==> "Q"       $ "As"
   , ["Q"]     ==> "P->Q"    $ "Ded"
   , []        ==> "P ? Q"   $ "As"
   , ["P->Q"]  ==> "R->P->Q" $ "Ded"
   , ["P ? Q"] ==> "R->P->Q" $ "Ded"
   ]
   
   
{-
ex :: Exercise (Proof String)
ex = emptyExercise
   { prettyPrinter = show
   , strategy = liftToContext $ label "proof" $ strategyGenerator exTranslator exDag2
   }

exTranslator :: Translator
exTranslator = (newId, newId, newId "goal")

main = printDerivations ex mempty

main1 = printDerivation ex mempty

go = mapM_ (print . fromJust . fromContext) $ applyAll (strategy ex) (inContext ex mempty)

count = length $ applyAll (strategy ex) (inContext ex mempty) -}