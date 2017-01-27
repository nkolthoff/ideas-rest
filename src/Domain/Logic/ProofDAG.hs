module Domain.Logic.ProofDAG 
   ( ProofDag, (==>), proofterms
   , strategyGenerator, makeDag, makeGoal, makeGoals
   , trimProofDag, relabel
   , goalSet, nodeMap, depends, simpleDepends, findMotivation
   ) where

import Control.Monad
import Data.List (intercalate, (\\), partition)
import Data.Maybe
import Domain.Logic.LinearProof hiding (Motivation, goal, label)
import Ideas.Common.Library
import qualified Domain.Logic.LinearProof as LP
import qualified Data.Map as M
import qualified Data.Set as S

infix 1 ==>

type Motivation l a = (l, [a])

-- invariant :: the motivation should not be empty
data ProofDag l a = PD
   { nodeMap :: M.Map a (S.Set (Motivation l a))
   , goalSet :: S.Set a
   } 
 deriving Eq
   
triplesInDag :: ProofDag l a -> [(a, l, [a])]
triplesInDag dag = 
   [ (a, l, as) 
   | (a, ms) <- M.toList (nodeMap dag) 
   , (l, as) <- S.toList ms
   ]
   
-- to do: report violations of the invariant
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
   in {- goalSet dag <> -} M.keysSet (nodeMap dag) {- <> S.fromList xs -}
    
relabel :: (Ord l2, Ord a) => (l1 -> Maybe l2) -> ProofDag l1 a -> ProofDag l2 a
relabel f dag = dag { nodeMap = M.filter (not . S.null) (M.map (S.fromList . concatMap g . S.toList) (nodeMap dag)) }
 where
   g (l1, xs) = case f l1 of
                   Just l2 -> [(l2, xs)]
                   Nothing -> []
                   
findMotivation :: Ord a => a -> ProofDag l a -> Motivation l a
findMotivation a dag = head $ S.toList $ fromJust $ M.lookup a (nodeMap dag)
    
makeDag :: Ord a => [a] -> Proof a -> ProofDag String a
makeDag gls p = mconcat $ makeGoals gls : mapMaybe f (prooflines p)
 where
   f pl = do 
      a  <- term pl
      xs <- mapM find (references pl)
      return (xs ==> a $ LP.label pl)
      
   find i = findNumber i p >>= term

trimProofDag :: Ord a => ProofDag l a -> ProofDag l a
trimProofDag dag 
   | S.null removals = dag
   | otherwise       = trimProofDag trimmed
  where 
    used = S.fromList (concatMap f (M.elems (nodeMap dag)))
    f ms = concatMap snd (S.toList ms)
    removals  = S.filter (notUsed) (M.keysSet (nodeMap dag))
    notUsed a = not (a `S.member` used) && not (a `S.member` (goalSet dag))
    trimmed   = dag { nodeMap = M.filterWithKey (\k _ -> not (k `S.member` removals)) (nodeMap dag) }

-- Een goal is een statement dat nog niet gemotiveerd is
-- Hou de volgende prioritering aan:
--
-- 1) sluiten van een bewijs voor een goal
--    -> motivatie toevoegen (als er meer zijn, kies voor laagste nr in bewijs)
-- 2) achteruit stappen (deductie stelling altijd een goed idee, MP niet zo heel gauw)
--    -> kies voor laatst toegevoegd (dus laagste nr in bewijs)
-- 3) gebruiken van statements die er al zijn (voorwaartse stap, is bijna altijd MP en niet Ded)
--    -> combineer regels die het laatst zijn toegevoegd (dus met hoogste nr; 1+4 beter dan 2+3)
-- 4) introduceren van een assumptie/axioma (lage prioriteit), dat zijn de regels zonder afhankelijkheid
--    -> welke ga ik gebruiken? slim zijn!
--          pak het laatst toegevoegde, gemotiveerde knoop (met hoogste nr)
--          kijk 1 stap vooruit, en vanuit daar wat je aan assumpties nodig hebt
--          

newGen :: (Ord a, Ord l, Show l) => [a] -> ProofDag l a -> Strategy (Proof a)
newGen grounded dag = 
   ( choice [ forw a l as  .*. newGen (a:grounded) dag | (a, l, as) <- forws1 ] ./. 
     choice [ forw a l as  .*. newGen (a:grounded) dag | (a, l, as) <- forws2 ] ./. 
     choice [ introNew a l .*. newGen (a:grounded) dag | (a, l) <- leafs1 ] ./. 
     choice [ introNew a l .*. newGen (a:grounded) dag | (a, l) <- leafs2 ]
   ) .|.
   check (\_ -> null leafs && null forws)
 where
   leafs = [ (a, l) | (a, l, as) <- triplesInDag dag, null as, a `notElem` grounded ]
   (leafs1, leafs2) = partition ((`elem` nextNodes). fst) leafs
   --
   forws = [ (a, l, as) | (a, l, as) <- triplesInDag dag, not (null as), a `notElem` grounded, all (`elem` grounded) as ]
   (forws1, forws2) = partition forwWithGrounded forws
   -- 
   nexts = case grounded of
               hd:_ -> [ a | (a, l, as) <- triplesInDag dag, hd `elem` as ]
               []   -> []
   nextDag   = trimProofDag dag {goalSet = S.fromList nexts}
   nextNodes = M.keys (nodeMap nextDag)
   --
   forwWithGrounded (a, l, as) = 
      case grounded of
         hd:_ -> hd `elem` as
         []   -> True

dag1 :: ProofDag String Int
dag1 = mconcat $
   [ []            ==> 1 $ "A"
   , []            ==> 2 $ "B"
   , [1, 2]        ==> 3 $ "C"
   , [2, 3]        ==> 4 $ "D"
   ]

testje = apply (newGen [] dag1) mempty


strategyGenerator :: (Ord a, Ord l, Show l, Show a) => ProofDag l a -> Strategy (Proof a)
strategyGenerator dag = untilS (null . getGoals) $
   choice [ closeStep i (a, l, as) | (i, (a, l, as)) <- uniques ] 
   |> (   choice [ backwardStep i (a, l, as) | (i, (a, l, as)) <- uniques ]
      ./. choice [ forwardStep  i (a, l, as) | (i, (a, l, as)) <- uniques ]
      ./. choice [ introStepDirect     dag l i | (l, i) <- zip ls [0..] ]
      ./. choice [ introStepTwos  twos dag l i | (l, i) <- zip ls [0..] ]     
      ./. choice [ introStep           dag l i | (l, i) <- zip ls [0..] ]
      )
 where
   triples = triplesInDag dag
   uniques = zip [0..] triples
 
   ls = S.toList (S.unions (map (S.map fst) (M.elems (nodeMap dag))))
   
   leafs = M.keysSet (M.filter (any (null . snd) . S.toList) (nodeMap dag))
   twos  = M.keysSet (M.filter (any (isTwo . snd) . S.toList) (nodeMap dag))
    where
      isTwo xs = not (null xs) && all (`S.member` leafs) xs

closeStep :: (Ord a, Show l, Eq l, Show a) => Int -> (a, l, [a]) -> Rule (Proof a)
closeStep i (a, l, as) = makeRule (show l # "close" # show i) $ \p -> do
   (goalnr, goal) <- getGoals p
   guard (goal == a)
   is <- mapM (\a -> maybeToList (findInProof a p >>= number)) as
   guard (all (< goalnr) is)
   return $ addMotivation goalnr (show l, is) p

backwardStep :: (Ord a, Show l, Eq l) => Int -> (a, l, [a]) -> Rule (Proof a)
backwardStep i (a, l, as) = makeRule (show l # "backward" # show i) $ \p -> do
   (goalnr, goal) <- getGoals p
   guard (goal == a)
   guard (length as == 1)
   let i = prevNumberBefore goalnr p
   return $ goalNr i (head as) <> addMotivation goalnr (show l, [i]) p

forwardStep :: (Ord a, Show l, Eq l, Show a) => Int -> (a, l, [a]) -> Rule (Proof a)
forwardStep i (a, l, as) = makeRule (show l # "forward" # show i) $ \p -> do
   guard (not (has a p))
   guard (not (null as))
   is <- mapM (\a -> maybeToList (findInProof a p >>= number)) as
   let i = nextNumberAfter (maximum (0:is)) p
   return $ prooflineNr i a (show l, is) <> p

introStepDirect :: (Ord a, Show l, Eq l) => ProofDag l a -> l -> Int -> Rule (Proof a)
introStepDirect dag = intro dag $ \a p -> 
   let directSet = any direct . S.toList
       direct (_, as) = a `elem` as && all (`has` p) (as \\ [a])
   in not (hasGrounded a p) && any directSet (M.elems (nodeMap dag))
      
introStepTwos :: (Ord a, Show l, Eq l) => S.Set a -> ProofDag l a ->  l -> Int -> Rule (Proof a)
introStepTwos twos dag = intro dag $ \a p ->
   let twoSet (b, s) = any (isTwo b) (S.toList s)
       isTwo b (_, as) = a `elem` as && b `S.member` twos
   in not (hasGrounded a p) && any twoSet (M.toList (nodeMap dag))
      
introStep :: (Ord a, Show l, Eq l) => ProofDag l a -> l -> Int -> Rule (Proof a)
introStep dag = intro dag $ \a p -> not (hasGrounded a p)

intro :: (Ord a, Show l, Eq l) => ProofDag l a -> (a -> Proof a -> Bool) -> l -> Int -> Rule (Proof a)
intro dag condition l0 i = makeRule (show l0 # "intro" # show i) $ \p -> do
   (a, mots) <- M.toList (nodeMap dag)
   guard (condition a p) -- check the condition
   (l, as)   <- S.toList mots
   guard (l == l0)
   guard (null as)
   is <- mapM (\a -> maybeToList (findInProof a p >>= number)) as
   let i = nextNumberAfter (maximum (0:is)) p
   return $ prooflineNr i a (show l, []) <> p

introNew :: Show l => a -> l -> Rule (Proof a)
introNew a l = makeRule (show l # "intro") $ \p -> do
   let i = nextNumber p
   Just $ prooflineNr i a (show l, []) <> p

forw :: (Show l, Eq a) => a -> l -> [a] -> Rule (Proof a)
forw a l as = makeRule (show l # "forw") $ \p -> do
   is <- mapM (\x -> maybeToList (findInProof x p >>= number)) as
   let i = nextNumberAfter (maximum (0:is)) p
   return $ prooflineNr i a (show l, is) <> p

has :: Eq a => a -> Proof a -> Bool
has a p = a `elem` mapMaybe term (prooflines p)

hasGrounded :: Eq a => a -> Proof a -> Bool
hasGrounded a p = a `elem` mapMaybe term (groundedLines p)
  where 
     groundedLines prf = takeWhile (motivated)  (prooflines prf)


unmotivated :: Proofline a -> Bool
unmotivated = null . LP.label

motivated :: Proofline a -> Bool
motivated p = not (unmotivated p)

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
        
simpleDepends :: Ord a => ProofDag l a -> a -> S.Set a
simpleDepends dag = S.fromList . rec
 where
   rec a = a : 
      [ c
      | (_, bs) <- maybe [] S.toList (M.lookup a (nodeMap dag)) 
      , b <- bs
      , c <- rec b
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