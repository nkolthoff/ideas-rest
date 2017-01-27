module Domain.Logic.LinearProof 
   ( -- Types
     Proof, Proofline, Motivation
     -- Getters
   , prooflines, number, term, label, references, motivation
   , findInProof, findInProofBy, findNumber
     -- Constructors
   , makeProof
   , goal, goalNr, proofline, prooflineNr
   , addAssumption, addProofline, addProoflineNr, merge, safeMerge
   , addMotivation
     -- Numbering
   , usedNumbers, nextNumber, nextNumberAfter, prevNumber, prevNumberBefore
     -- Checks
   , checkLabels, checkOrder
     -- Transformations
   , renumber, renumberFrom, renumberWith, autonumber, autonumberWith, reorder 
   , stripProof, stripProofBy
   ) where

import Control.Monad
import Data.List
import Data.Maybe
import Data.Monoid
import Ideas.Common.Rewriting.Term
import Ideas.Text.JSON
import Ideas.Text.Latex

data Proof a = P { prooflines :: [Proofline a] }
 deriving Eq

data Proofline a = PL
   { number     :: Maybe Int
   , term       :: Maybe a
   , label      :: String
   , references :: [Int]
   }
 deriving Eq
 
type Motivation = (String, [Int])
 
makeProof :: [Proofline a] -> Proof a
makeProof = P
 
motivation :: Proofline a -> Motivation
motivation pl = (label pl, references pl)
   
goal :: a -> Proof a
goal a = proofline a ([], [])

goalNr :: Int -> a -> Proof a
goalNr n a = prooflineNr n a ([], [])

proofline :: a -> Motivation -> Proof a
proofline a (s, ns) = P [PL Nothing (Just a) s ns]

prooflineNr :: Int -> a -> Motivation -> Proof a
prooflineNr n a (s, ns) = P [PL (Just n) (Just a) s ns]

-- auto number
addAssumption :: a -> Proof a -> Proof a
addAssumption a = addProofline a [] []

-- auto number
addProofline :: a -> String -> [Int] -> Proof a -> Proof a
addProofline a s ns proof = P $ 
   PL (Just (nextNumber proof)) (Just a) s ns : prooflines proof

addProoflineNr :: Int -> a -> String -> [Int] -> Proof a -> Proof a
addProoflineNr n a s ns proof = P $ 
   PL (Just n) (Just a) s ns : prooflines proof

addMotivation :: Int -> Motivation -> Proof a -> Proof a
addMotivation n (s, is) = makeProof . map f . prooflines
 where
   f pl | number pl == Just n = pl { label = s, references = is }
        | otherwise           = pl

instance Functor Proof where
   fmap f (P xs) = P (map (fmap f) xs)

instance Functor Proofline where
   fmap f s = s { term = fmap f (term s) }

instance Monoid (Proof a) where
   mempty  = P []
   mappend = merge

instance Show a => Show (Proof a) where
   show = unlines . map show . prooflines
   
instance Show a => Show (Proofline a) where
   show pl = s2 ++ s4
    where
      s1 = maybe "" ((++ ".") . show) (number pl)
      s2 = alignr 5 s1 ++ "  " ++ maybe "" show (term pl)
      s3 = intercalate ", " (label pl : map show (references pl))
      s4 = if null s3 then "" else "  " ++ alignr (70 - length s2) (bracket s3)
      
      alignr n x = replicate (n - length x) ' ' ++ x
      bracket s  = "[" ++ s ++ "]"

instance InJSON a => InJSON (Proof a) where
   toJSON   = toJSON . prooflines
   fromJSON = liftM makeProof . fromJSON
   
instance InJSON a => InJSON (Proofline a) where
   toJSON pl = Object $ concat
      [ [ ("number", toJSON n) | n <- maybeToList (number pl) ]
      , [ ("term", toJSON t) | t <- maybeToList (term pl) ]
      , [ ("label", toJSON (label pl)) | not (null (label pl)) ]
      , [ ("references", toJSON (references pl)) | not (null (references pl)) ]
      ]
   fromJSON json = return (PL mnr mterm lab refs)
    where
      mnr   = lookupM "number"     json >>= fromJSON
      mterm = lookupM "term"       json >>= fromJSON
      lab   = lookupM "label"      json >>= fromMaybe "" . fromJSON
      refs  = lookupM "references" json >>= fromMaybe [] . fromJSON

proofSymbol, prooflineSymbol :: Symbol
proofSymbol     = newSymbol "proof"
prooflineSymbol = newSymbol "proofline"

instance IsTerm a => IsTerm (Proof a) where
   toTerm = function proofSymbol . map toTerm . prooflines
   fromTerm (TCon s xs) | s == proofSymbol = 
      fmap makeProof (mapM fromTerm xs)
   fromTerm _ = fail "fromTerm proof"

instance IsTerm a => IsTerm (Proofline a) where
   toTerm pl = function prooflineSymbol 
      [toTerm (number pl), toTerm (term pl), TVar (label pl), toTerm (references pl)]
   
   fromTerm (TCon s [t1, t2, t3, t4]) | s == prooflineSymbol = do
      nr  <- fromTerm t1
      t   <- fromTerm t2
      lab <- fromTerm t3
      is  <- fromTerm t4
      return (PL nr t lab is)
   fromTerm _ = fail "fromTerm proofline"

instance ToLatex a => ToLatex (Proof a) where
   toLatex = toLatex . prooflines

instance ToLatex a => ToLatex (Proofline a) where
   toLatex x = toLatexList [x]
   toLatexList = array "rll" . map f
    where
      f pl = [numberTex (number pl), toLatex (term pl), motTex (motivation pl)]

      numberTex = toLatex . fmap ((++ ".") . show)
      motTex (s, is) = commas (toLatex s : map toLatex is)

usedNumbers :: Proof a -> [Int]
usedNumbers = nub . concatMap f . prooflines
 where
   f s = maybe id (:) (number s) (references s)

nextNumber :: Proof a -> Int
nextNumber = nextNumberAfter 0

nextNumberAfter :: Int -> Proof a -> Int
nextNumberAfter n p = head (filter (`notElem` usedNumbers p) [n+1 ..])

prevNumber :: Proof a -> Int
prevNumber = prevNumberBefore 1001

prevNumberBefore :: Int -> Proof a -> Int
prevNumberBefore n p = head (filter (`notElem` usedNumbers p) [n-1, n-2 ..])

getProofline :: Proof a -> Int -> Maybe (Proofline a)
getProofline proof n =
   case filter ((== Just n) . number) (prooflines proof) of
      [s] -> Just s
      _   -> Nothing

checkLabels :: [(String, [a] -> a -> Bool)] -> Proof a -> Bool
checkLabels env proof = all checkProofline (prooflines proof)
 where
   checkProofline s = fromMaybe False $ do
      a  <- term s
      f  <- lookup (label s) env
      xs <- mapM (getProofline proof) (references s) 
      ys <- mapM term xs
      return (f ys a)
 
checkOrder :: Proof a -> Bool
checkOrder proof = rec [] (prooflines proof)
 where
   rec _  []     = True
   rec ns (s:ss) = 
      all (`elem` ns) (references s) && 
      rec (maybe id (:) (number s) ns) ss 

renumber :: Proof a -> Proof a
renumber = renumberFrom 1

renumberFrom :: Int -> Proof a -> Proof a
renumberFrom i proof = renumberWith f proof
 where
   used = usedNumbers proof
   f    = fromMaybe 0 . (`lookup` zip used [i..])

renumberWith :: (Int -> Int) -> Proof a -> Proof a
renumberWith f proof = proof { prooflines = map g (prooflines proof) }
 where
   g s = s 
      { number     = fmap f (number s)
      , references = fmap f (references s)
      }
      
autonumber :: Proof a -> Proof a
autonumber = autonumberWith [1..]

autonumberWith :: [Int] -> Proof a -> Proof a
autonumberWith ns0 proof = proof { prooflines = rec ns (prooflines proof) }
 where
   ns   = filter (`notElem` used) ns0
   used = usedNumbers proof
   
   rec (i:is) (x:xs)
      | isNothing (number x) = x {number = Just i} : rec is xs 
      | otherwise            = x : rec (i:is) xs
   rec _ [] = []
   rec [] _ = error "out of numbers"


-- merge two proofs: there should not be an overlap in line numbers
merge :: Proof a -> Proof a -> Proof a
merge p1 p2 = P (rec (prooflines p1) (prooflines p2))
 where
   rec [] ys = ys
   rec xs [] = xs
   rec (x:xs) (y:ys) =
      case (number x, number y) of 
         (Nothing, _)   -> x : rec xs (y:ys)
         (_, Nothing)   -> y : rec (x:xs) ys
         (Just i, Just j)
            | i <= j    -> x : rec xs (y:ys)
            | otherwise -> y : rec (x:xs) ys

-- merge proofs; renumber the second part, where necessary
safeMerge :: Proof a -> Proof a -> Proof a
safeMerge p1 p2 = p1 <> renumberWith f p2
 where
   used1 = usedNumbers p1
   used2 = usedNumbers p2
   used  = used1 `union` used2
   clash = used1 `intersect` used2
   fresh = filter (`notElem` used) [1..]
   table = zip clash fresh
   f x   = fromMaybe x (lookup x table)

reorder :: Proof a -> Proof a
reorder proof = proof { prooflines = f start }
 where
   start = [ (s, references s) | s <- prooflines proof ]
   f xs 
      | null xs   = []
      | null xs1  = f ((fst (head xs), []) : tail xs) -- break circularity
      | otherwise = map fst xs1 ++ f (map remove xs2)
    where
      (xs1, xs2) = partition (null . snd) xs
      new = mapMaybe (number . fst) xs1
      remove (s, is) = (s, filter (`notElem` new) is)
      
stripProof :: Eq a => a -> Proof a -> Proof a
stripProof a p = p 
   { prooflines = filter (maybe False (`elem` is). number) (prooflines p) } 
 where
   is = maybe [] f (findInProof a p)
   f pl = maybeToList (number pl) ++ concatMap g (references pl)
   g i  = maybe [] f (findNumber i p)
   
stripProofBy :: (a -> Bool) -> Proof a -> Proof a
stripProofBy cond p = p 
   { prooflines = filter (maybe False (`elem` is). number) (prooflines p) } 
 where
   is = maybe [] f (findInProofBy cond p)
   f pl = maybeToList (number pl) ++ concatMap g (references pl)
   g i  = maybe [] f (findNumber i p)
   
findInProof :: Eq a => a -> Proof a -> Maybe (Proofline a)
findInProof a p = listToMaybe $ 
   filter (maybe False (== a) . term) (prooflines p)

findInProofBy :: (a -> Bool) -> Proof a -> Maybe (Proofline a)
findInProofBy cond p = listToMaybe $ 
   filter (maybe False cond . term) (prooflines p)

findNumber :: Int -> Proof a -> Maybe (Proofline a)
findNumber i p = listToMaybe $ 
   filter (maybe False (== i) . number) (prooflines p)