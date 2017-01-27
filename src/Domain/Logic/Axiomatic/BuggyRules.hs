module Domain.Logic.Axiomatic.BuggyRules (buggyRules) where

import Data.Maybe
import Ideas.Common.Library hiding (label)
import Domain.Logic.Axiomatic.Statement
import Domain.Logic.LinearProof
import Domain.Logic.Axiomatic.Rules hiding (exProof)
import Domain.Logic.Formula
import qualified Data.Set as S
import Control.Monad
import Domain.Logic.Parser
import Ideas.Utils.Prelude
import Data.Typeable

-- order in the list determines in which order the buggy rules are tried
buggyRules :: [Rule (Proof Statement)]
buggyRules = [bugMPfw2,bugMPfw3,bugMPfw4,bugMPfw5, bugMPfw6, bugMPfw7,bugMPfw8,
              bugMPm1, bugMPm2, bugMPm3, bugMPm4,
              bugMPcl1,bugMPcl2, bugMPcl3,bugMPcl4, bugMPcl5, bugMPcl6, bugMPcl7,bugMPcl8,
              bugMPDefault,bugMPDefault2, 
              bugDedcl4,bugDedcl1, bugDed1, bugDedcl2, bugDedcl3 
             ]

checkInput2 r1 r2 f = transInput2 r1 r2 $ \x y p -> if f x y p then Just p else Nothing
checkInput3 r1 r2 r3 f = transInput3 r1 r2 r3 $ \x y z p -> if f x y z p then Just p else Nothing

transCheck :: (a -> Bool) -> Transformation a
transCheck p = makeTrans $ \x -> [x | p x]

checkInOut :: Trans a i -> Trans o x -> Trans (i, a) o -> Transformation a
checkInOut inT outT = outputOnlyWith outT . inputWith inT

readRef3M :: Ref a -> Ref b -> Ref c -> Trans x (a, b, Maybe c)
readRef3M r1 r2 r3 = (readRef2 r1 r2) &&& readRefMaybe r3 >>> arr f
  where
   f ((a, b), c) = (a, b, c)
{-  niet nodig? 
readRef3M2 :: Ref a -> Ref b -> Ref c -> Trans x (Maybe c, b, a)
readRef3M2 r1 r2 r3 = (transReadRefM r3 &&& readRef r2) &&& readRef r1 >>> arr f
  where
   f ((a, b), c) = (a, b, c)   

readRef3M1 :: Ref a -> Ref b -> Ref c -> Trans x (Maybe a, b, c)
readRef3M1 r1 r2 r3 = (transReadRefM r1 &&& readRef r2) &&& readRef r3 >>> arr f
  where
   f ((a, b), c) = (a, b, c)
-}

-- Buggy rules
{- is gelijk aan buggy-fw6
bugMPfw1 :: Rule (Proof Statement)
bugMPfw1 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw1") $ mustHaveParameters f (0, 0)
 where
   f = parameter2 "n1" "n2" $ \x y ->
      transCheck (mpForwardBug1 x y)

mpForwardBug1 :: Int -> Int -> Proof Statement -> Bool
mpForwardBug1 n1 n2 prf = fromMaybe False $ do
   st1 <- findNumber n1 prf >>= term
   st2 <- findNumber n2 prf >>= term
   return (fits (consequent st1) (consequent st2))
 where
   fits (p :->: q) r | q == r && p /= q = True
   fits p (q :->: r) | p == r && q /= r = True
   fits _ _ = False
-}
{-
bugMPfw2 :: Rule (Proof Statement)
bugMPfw2 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw2") $
   transLookup2 n1Ref n2Ref $ \x y ->
      transCheck (mpForwardBug2 x y)
-}      
bugMPfw2 :: Rule (Proof Statement)
bugMPfw2 = describe "buggy mp" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw2") $
   checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef2 phiRef psiRef) mpForwardBug22         

mpForwardBug2 :: Int -> Int -> Proof Statement -> Bool
mpForwardBug2 n1 n2 prf = fromMaybe False $ do
   pl <- findNumber n1 prf
   guard (not(null (label pl)))
   st1 <- term pl
   st2 <- findNumber n2 prf >>= term
   let cs1 = consequent st1
       cs2 = consequent st2
   return (inImpl cs1 cs2)
 where
   inImpl q (p :->: (r :->:s)) = p /= q && q == r
   inImpl _ _ = False   
   
mpForwardBug22 :: Trans ((Int, Int, Maybe Int), Proof Statement) (SLogic, SLogic)
mpForwardBug22 = makeTrans $ \((n1, n2, mn3), prf) -> do
   pl <- findNumber n1 prf
   guard (isNothing mn3)
   st1 <- term pl
   st2 <- findNumber n2 prf >>= term
   let cs1 = consequent st1
       cs2 = consequent st2
   guard (inImpl cs1 cs2)
   return (xs cs1 cs2)
 where
   inImpl q (p :->: (r :->:s)) = p /= q && q == r
   inImpl _ _ = False   
   xs q (p :->: (r :->:s)) = (q, p)
{-   
bugMPfw3 :: Rule (Proof Statement)
bugMPfw3 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw3") $
   transLookup2 n1Ref n2Ref $ \x y ->
      transCheck (mpForwardBug3 x y)
-}   
bugMPfw3 :: Rule (Proof Statement)
bugMPfw3 = describe "buggy mp" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw3") $
   checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef2 phiRef psiRef) mpForwardBug32       

mpForwardBug3 :: Int -> Int -> Proof Statement -> Bool
mpForwardBug3 n1 n2 prf = fromMaybe False $ do
   pl <- findNumber n1 prf
   guard (not(null (label pl)))
   st1 <- term pl
   st2 <- findNumber n2 prf >>= term
   let cs1 = consequent st1
       cs2 = consequent st2
   return (transImpl cs1 cs2)
 where
   transImpl (p :->:q) (r :->:s) = q == r
   transImpl _ _ = False      
   
mpForwardBug32 ::  Trans ((Int, Int, Maybe Int), Proof Statement) (SLogic, SLogic)
mpForwardBug32 = makeTrans $ \((n1, n2, mn3), prf) -> do
   pl <- findNumber n1 prf
   guard (isNothing mn3)
   st1 <- term pl
   st2 <- findNumber n2 prf >>= term
   let cs1 = consequent st1
       cs2 = consequent st2
   guard (transImpl cs1 cs2)
   return (xs cs1 cs2)
 where
   transImpl (p :->:q) (r :->:s) = q == r
   transImpl _ _ = False      
   xs p (q :->:r) = (p, q)
{-   
bugMPcl3 :: Rule (Proof Statement)
bugMPcl3 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl3") $
   transLookup3 n1Ref n2Ref n3Ref $ \x y z ->
         transCheck (mpForwardBug3 z y)
-}         
bugMPcl3 :: Rule (Proof Statement)
bugMPcl3 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl3") $
   checkInOut (readRef3M n3Ref n2Ref nRef) (writeRef2 phiRef psiRef) mpForwardBug32            

bugMPfw4 :: Rule (Proof Statement)
bugMPfw4 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw4") $
   checkInput2 n1Ref n2Ref mpForwardBug4

mpForwardBug4 :: Int -> Int -> Proof Statement -> Bool
mpForwardBug4 n1 n2 prf = fromMaybe False $ do
   pl <- findNumber n1 prf
   guard (not(null (label pl)))
   st1 <- term pl
   st2 <- findNumber n2 prf >>= term
   let cs1 = consequent st1
       cs2 = consequent st2
   return (haakjesImpl cs1 cs2)
 where
   haakjesImpl (p :->:q) (r :->:(s :->: t)) = p == r && q == s
   haakjesImpl _ _ = False
   
 
bugMPcl4 :: Rule (Proof Statement)
bugMPcl4 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl4") $
   checkInput3 n1Ref n2Ref n3Ref $ \x y z -> mpForwardBug4 z y
{- 
bugMPfw5 :: Rule (Proof Statement)
bugMPfw5 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw5") $
   transLookup2 n1Ref n2Ref $ \x y ->
      transCheck (mpForwardBug5 x y)
-}      
bugMPfw5 :: Rule (Proof Statement)
bugMPfw5 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw5") $
   checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef2 phiRef psiRef) mpForwardBug52   

mpForwardBug5 :: Int -> Int -> Proof Statement -> Bool
mpForwardBug5 n1 n2 prf = fromMaybe False $ do
   pl <- findNumber n1 prf
   guard (not(null (label pl)))
   st1 <- term pl
   st2 <- findNumber n2 prf >>= term
   let cs1 = consequent st1
       cs2 = consequent st2
   return (equImpl cs1 cs2)
 where
   equImpl r (p :->:q)  = p /= r && (eqLogic p r)
   equImpl _ _ = False    
   
mpForwardBug52 :: Trans ((Int, Int, Maybe Int), Proof Statement) (SLogic, SLogic)
mpForwardBug52 = makeTrans $ \((n1, n2, mn3), prf) -> do
   pl <- findNumber n1 prf
   guard (isNothing mn3)
   st1 <- term pl
   st2 <- findNumber n2 prf >>= term
   let cs1 = consequent st1
       cs2 = consequent st2
   guard (equImpl cs1 cs2)
   return (xs cs1 cs2)
 where
   equImpl r (p :->:q)  = p /= r && (eqLogic p r)
   equImpl _ _ = False       
   xs r (p :->:q) = (r, p)

bugMPcl5 :: Rule (Proof Statement)
bugMPcl5 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl5") $
   checkInOut (readRef3M n3Ref n2Ref nRef) (writeRef2 phiRef psiRef) mpForwardBug52 
{-   
bugMPcl5 :: Rule (Proof Statement)
bugMPcl5 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl5") $
   transLookup3 n1Ref n2Ref n3Ref $ \x y z ->
         transCheck (mpForwardBug5 z y)
-}         
{-   
bugMPfw6 :: Rule (Proof Statement)
bugMPfw6 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw6") $
   transLookup2 n1Ref n2Ref $ \x y ->
      transCheck (mpForwardBug6 x y)
-}      
bugMPfw6 :: Rule (Proof Statement)
bugMPfw6 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw6") $
   checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef2 phiRef psiRef) mpForwardBug62         

mpForwardBug6 :: Int -> Int -> Proof Statement -> Bool
mpForwardBug6 n1 n2 prf = fromMaybe False $ do
   pl <- findNumber n1 prf
   guard (not(null (label pl)))
   st1 <- term pl
   st2 <- findNumber n2 prf >>= term
   let cs1 = consequent st1
       cs2 = consequent st2
   return (right cs1 cs2)
 where
   right r (p :->:q)  = p /= r && (r == q)
   right _ _ = False    
   
mpForwardBug62 :: Trans ((Int, Int, Maybe Int), Proof Statement) (SLogic, SLogic)
mpForwardBug62 = makeTrans $ \((n1, n2, mn3), prf) -> do
   pl <- findNumber n1 prf
   guard (isNothing mn3)
   st1 <- term pl
   st2 <- findNumber n2 prf >>= term
   let cs1 = consequent st1
       cs2 = consequent st2
   guard (right cs1 cs2)
   return (xs cs1 cs2) 
 where
   right r (p :->:q)  = p /= r && (r == q)
   right _ _ = False      
   xs r (p :->:q) = (r, p)
{-   
bugMPcl6 :: Rule (Proof Statement)
bugMPcl6 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl6") $
   transLookup3 n1Ref n2Ref n3Ref $ \x y z ->
         transCheck (mpForwardBug6 z y)
-}         
bugMPcl6 :: Rule (Proof Statement)
bugMPcl6 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl6") $
   checkInOut (readRef3M n3Ref n2Ref nRef) (writeRef2 phiRef psiRef) mpForwardBug62         
         
bugMPfw7 :: Rule (Proof Statement)
bugMPfw7 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw7") $ 
   checkInput2 n1Ref n2Ref mpForwardBug7

mpForwardBug7 :: Int -> Int -> Proof Statement -> Bool
mpForwardBug7 n1 n2 prf = fromMaybe False $ do
   pl <- findNumber n1 prf
   guard (not(null (label pl)))
   st1 <- term pl
   st2 <- findNumber n2 prf >>= term
   let cs1 = consequent st1
       cs2 = consequent st2
   return (haakjes cs1 cs2)
 where
   haakjes r ((p :->:q):->: s)  = p == r 
   haakjes _ _ = False    
   
   
bugMPcl7 :: Rule (Proof Statement)
bugMPcl7 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl7") $
   checkInput3 n1Ref n2Ref n3Ref $ \x y z -> mpForwardBug7 z y
{-         
bugMPfw8 :: Rule (Proof Statement)
bugMPfw8 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw8") $
   transLookup2 n1Ref n2Ref $ \x y ->
   transLookupM1 n3Ref $ \z -> 
      transCheck (mpForwardBug8 x y z)
-}      
bugMPfw8 :: Rule (Proof Statement)
bugMPfw8 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-fw8") $
   checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef psiRef) mpForwardBug82      

mpForwardBug8 :: Int -> Int -> Maybe Int -> Proof Statement -> Bool
mpForwardBug8 n1 n2 mn3 prf = fromMaybe False $ do
   pl <- findNumber n1 prf
   guard (isNothing mn3)
   guard (not(null (label pl)))
   st1 <- term pl
   st2 <- findNumber n2 prf >>= term
   let cs2 = consequent st2
   return (noImpl cs2)
 where
   noImpl (p :->:q)  = False 
   noImpl _         = True    
   
mpForwardBug82 :: Trans ((Int, Int, Maybe Int), Proof Statement) SLogic
mpForwardBug82 = makeTrans $ \((n1, n2, mn3), prf) -> do
   pl <- findNumber n1 prf
   guard (isNothing mn3)
   st1 <- term pl
   st2 <- findNumber n2 prf >>= term
   let cs2 = consequent st2
   guard (noImpl cs2)
   return cs2
 where
   noImpl (p :->:q)  = False 
   noImpl _         = True       
{-   
bugMPcl8 :: Rule (Proof Statement)
bugMPcl8 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl8") $
   transLookup3 n1Ref n2Ref n3Ref $ \x y z ->
         transCheck (mpForwardBug8 z y (Just x))
-}         
bugMPcl8 :: Rule (Proof Statement)
bugMPcl8 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl8") $
   checkInOut (readRef3M n3Ref n2Ref nRef) (writeRef psiRef) mpForwardBug82          
       
{-         
bugMPm1 :: Rule (Proof Statement)
bugMPm1 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-m1") $
   transLookup2 n1Ref n2Ref $ \x y ->
      transCheck (mpMid1 x y)
-}      
bugMPm1 :: Rule (Proof Statement)
bugMPm1 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-m1") $
   checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef asRef) mpMid12     

mpMid1 :: Int -> Int -> Proof Statement -> Bool
mpMid1 n1 n2 prf = fromMaybe False $ do
   st1 <- findNumber n2 prf >>= term
   pl <- findNumber n1 prf
   guard (null (label pl))
   st2 <- term pl
   let as1 = assumptions st1
       as2 = assumptions st2
       cs1 = consequent st1
       cs2 = consequent st2
   return ((fits cs1 cs2)&&  (not (as1 `S.isSubsetOf` as2)))
 where
   fits (p :->: q) r = q == r 
   fits _ _ = False   
   
mpMid12 :: Trans ((Int, Int, Maybe Int), Proof Statement) [SLogic]
mpMid12 = makeTrans $ \((n1, n2, mn3), prf) -> do
   st1 <- findNumber n2 prf >>= term
   pl <- findNumber n1 prf
   guard (null (label pl) && (isNothing mn3))
   st2 <- term pl
   let as1 = assumptions st1
       as2 = assumptions st2
       cs1 = consequent st1
       cs2 = consequent st2
   guard ((fits cs1 cs2)&&  (not (as1 `S.isSubsetOf` as2)))
   return $ S.toList (S.difference as1 as2)
 where
   fits (p :->: q) r = q == r 
   fits _ _ = False     
   
bugMPm2 :: Rule (Proof Statement)
bugMPm2 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-m2") $
   checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef asRef) mpMid22    
{-   
bugMPm2 :: Rule (Proof Statement)
bugMPm2 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-m2") $
   transLookup2 n1Ref n2Ref $ \x y ->
      transCheck (mpMid2 x y)
-}
mpMid2 :: Int -> Int -> Proof Statement -> Bool
mpMid2 n1 n2 prf = fromMaybe False $ do
   st1 <- findNumber n2 prf >>= term
   pl <- findNumber n1 prf
   guard (null (label pl))
   st2 <- term pl
   let as1 = assumptions st1
       as2 = assumptions st2
   return  (not (as1 `S.isSubsetOf` as2))
   
mpMid22 :: Trans ((Int, Int, Maybe Int), Proof Statement) [SLogic]
mpMid22 = makeTrans $ \((n1, n2, mn3), prf) -> do
   st1 <- findNumber n2 prf >>= term
   pl <- findNumber n1 prf
   guard (null (label pl) && (isNothing mn3))
   st2 <- term pl
   let as1 = assumptions st1
       as2 = assumptions st2
   guard  (not (as1 `S.isSubsetOf` as2))  
   return $ S.toList (S.difference as1 as2)

bugMPm3 :: Rule (Proof Statement)
bugMPm3 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-m3") $
   checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef phiRef) mpMid32  
{-   
bugMPm3 :: Rule (Proof Statement)
bugMPm3 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-m3") $
   transLookup2 n1Ref n2Ref $ \x y ->
     transCheck (mpMid3 x y)
-}
mpMid3 :: Int -> Int -> Proof Statement -> Bool
mpMid3 n1 n2 prf = fromMaybe False $ do
   st1 <- findNumber n2 prf >>= term
   pl <- findNumber n1 prf
   guard (null (label pl))
   let cs1 = consequent st1
   return (noImpl cs1)
 where
   noImpl (p :->:q)  = False 
   noImpl _         = True    
   
mpMid32 :: Trans ((Int, Int, Maybe Int), Proof Statement) SLogic
mpMid32 = makeTrans $ \((n1, n2, mn3), prf) -> do
   st1 <- findNumber n2 prf >>= term
   pl <- findNumber n1 prf
   guard (null (label pl) && (isNothing mn3))
   let cs1 = consequent st1
   guard(noImpl cs1)
   return cs1
 where
   noImpl (p :->:q)  = False 
   noImpl _         = True       
{-   
bugMPm4 :: Rule (Proof Statement)   
bugMPm4 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-m4") $
   transLookup2 n1Ref n2Ref $ \x y ->
      transCheck (mpMid4 x y)
-}      
bugMPm4 :: Rule (Proof Statement)
bugMPm4 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-m4") $
   checkInOut (readRef3M n1Ref n2Ref n3Ref) (writeRef2 phiRef psiRef) mpMid42  

mpMid4 :: Int -> Int -> Proof Statement -> Bool
mpMid4 n1 n2 prf = fromMaybe False $ do
   st1 <- findNumber n2 prf >>= term
   pl <- findNumber n1 prf
   guard (null (label pl))
   st2 <- term pl
   let 
       cs1 = consequent st1
       cs2 = consequent st2
   return (nofits cs1 cs2)
 where
   nofits (p :->: q) r = q /= r 
   nofits _ _ = False  
   
mpMid42 :: Trans ((Int, Int, Maybe Int), Proof Statement) (SLogic, SLogic)
mpMid42 = makeTrans $ \((n1, n2, mn3), prf) -> do
   st1 <- findNumber n2 prf >>= term
   pl <- findNumber n1 prf
   guard (null (label pl)&& (isNothing mn3))
   st2 <- term pl
   let 
       cs1 = consequent st1
       cs2 = consequent st2
   guard (nofits cs1 cs2)
   return (xs cs1 cs2)
 where
   nofits (p :->: q) r = q /= r 
   nofits _ _ = False     
   xs (p :->: q) r = (q, r)
{-   
bugMPcl1 :: Rule (Proof Statement)
bugMPcl1 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl1") $
   transLookup3 n1Ref n2Ref n3Ref $ \x y z ->
      transCheck (mpCloseBug1 x y z)
-}     
bugMPcl1 :: Rule (Proof Statement)
bugMPcl1 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl1") $
   checkInOut (readRef3 n1Ref n2Ref n3Ref) (writeRef asRef) mpCloseBug12   

-- in een applicatie van MP (phi, phi -> psi, psi) is psi = n1 en phi = n3
mpCloseBug1 :: Int -> Int -> Int -> Proof Statement  -> Bool
mpCloseBug1 n1 n2 n3 prf =  fromMaybe False $ do
   st1 <- findNumber n3 prf >>= term
   st2 <- findNumber n2 prf >>= term
   st3 <- findNumber n1 prf >>= term
   let as1 = assumptions st1
       as2 = assumptions st2
       as3 = assumptions st3
   return ((nosubs as1 as2 as3)&&  ( fits (consequent st3) (consequent st1) (consequent st2))) 
  where
   nosubs as1 as2 as3 = not (S.union as1 as2  `S.isSubsetOf` as3) 
   fits q (p :->: r) (s :->: t) =  (q == r && p == (s :->: t)) ||(q == t && s == (p :->: q))
   fits q (p :->: r) s  = q == r && p == s
   fits q s (p :->: r) = q == r && p == s
   fits _ _ _ = False

   
mpCloseBug12 :: Trans ((Int, Int, Int), Proof Statement) [SLogic]
mpCloseBug12 = makeTrans $ \((n1, n2, n3), prf) -> do   
   st1 <- findNumber n3 prf >>= term
   st2 <- findNumber n2 prf >>= term
   st3 <- findNumber n1 prf >>= term
   let as1 = assumptions st1
       as2 = assumptions st2
       as3 = assumptions st3
   guard ((nosubs as1 as2 as3) &&  ( fits (consequent st3) (consequent st1) (consequent st2))) 
   return  $ S.toList as3
  where
   nosubs as1 as2 as3 = not (S.union as1 as2  `S.isSubsetOf` as3) 
   fits q (p :->: r) (s :->: t) =  (q == r && p == (s :->: t)) ||(q == t && s == (p :->: q))
   fits q (p :->: r) s  = q == r && p == s
   fits q s (p :->: r) = q == r && p == s
   fits _ _ _ = False   
   
{-  
bugMPcl2 :: Rule (Proof Statement)
bugMPcl2 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl2") $
   transLookup3 n1Ref n2Ref n3Ref $ \x y z ->
      transCheck (mpCloseBug2 x y z)
-}   

 
bugMPcl2 :: Rule (Proof Statement)
bugMPcl2 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-cl2") $
   checkInOut (readRef3 n1Ref n2Ref n3Ref) (writeRef2 phiRef psiRef) mpCloseBug22   

mpCloseBug2 :: Int -> Int -> Int -> Proof Statement -> Bool
mpCloseBug2 n1 n2 n3 prf = fromMaybe False $ do
   st1 <- findNumber n3 prf >>= term
   st2 <- findNumber n2 prf >>= term
   st3 <- findNumber n1 prf >>= term
   let cs1 = consequent st1
       cs2 = consequent st2
       cs3 = consequent st3
   return (inImpl cs1 cs2 cs3)
 where
   inImpl q (p  :->: (r :->:s)) (x :->: y) = q == r && p == x && s == y
   inImpl _ _ _= False  
  
mpCloseBug22 :: Trans ((Int, Int, Int), Proof Statement) (SLogic, SLogic)
mpCloseBug22 = makeTrans $ \((n1, n2, n3), prf) -> do 
   st1 <- findNumber n3 prf >>= term
   st2 <- findNumber n2 prf >>= term
   st3 <- findNumber n1 prf >>= term
   let cs1 = consequent st1
       cs2 = consequent st2
       cs3 = consequent st3
   guard (inImpl cs1 cs2 cs3)
   return (xs cs1 cs2)
 where
   inImpl q (p :->: (r :->:s)) (x :->: y) = q == r && p == x && s == y
   inImpl _ _ _= False     
   xs q (p :->: (r :->:s)) = (q, p)
   
   
  

bugMPDefault :: Rule (Proof Statement)
bugMPDefault = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-default") $
   checkInput3 n1Ref n2Ref n3Ref $ \x y z -> mpDefaultBug z y x
   
mpDefaultBug :: Int -> Int -> Int -> Proof Statement -> Bool
mpDefaultBug n1 n2 n3 prf = True

bugMPDefault2 :: Rule (Proof Statement)
bugMPDefault2 = describe "buggy MP" $ buggy $ siblingOf mpId $ ruleTrans (mpId # "buggy-default2") $
   checkInput2 n1Ref n2Ref mpDefaultBug2
   
mpDefaultBug2 ::  Int -> Int -> Proof Statement -> Bool
mpDefaultBug2 n1 n2  prf = True

bugDed1 :: Rule (Proof Statement)
bugDed1 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggy-1") $
   checkInOut (readRef nRef) (writeRef phiRef) dedBug2

dedBug2 :: Trans (Int, Proof Statement) SLogic
dedBug2 = makeTrans $ \(n, prf) -> do
   st <- findNumber n prf >>= term
   let cs = consequent st
   guard (noImpl cs) 
   return cs
  where
   noImpl (p :->: q) = False 
   noImpl _          = True
 
dedBug:: Int -> Proof Statement -> Maybe Environment
dedBug n  prf = do
   st <- findNumber n prf >>= term
   let cs = consequent st
   guard (noImpl cs) 
   return (singleBinding phiRef cs)
  where
   noImpl (p :->: q) = False 
   noImpl _          = True
{-   
bugDedcl1 :: Rule (Proof Statement)
bugDedcl1 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggy-2") $
   transLookup2 n1Ref n2Ref $ \x y ->
      transCheck (dedBugcl1 x y)
-}   
dedBugcl1::Int -> Int -> Proof Statement  -> Bool
dedBugcl1 n1 n2  prf =  fromMaybe False $ do
   st <- findNumber n2 prf >>= term
   let cs = consequent st
   return (noImpl cs) 
  where
   noImpl (p :->: q) = False 
   noImpl _          = True
   
bugDedcl1 :: Rule (Proof Statement)
bugDedcl1 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggy-2") $
   checkInOut (readRef2 n1Ref n2Ref) (writeRef phiRef) dedBugcl12      
   
dedBugcl12::Trans ((Int, Int), Proof Statement) SLogic
dedBugcl12 = makeTrans $ \((n1, n2), prf) -> do
    st <- findNumber n2 prf >>= term
    let cs = consequent st
    guard (noImpl cs) 
    return cs
  where
    noImpl (p :->: q) = False 
    noImpl _          = True
{- 
bugDedcl2 :: Rule (Proof Statement)
bugDedcl2 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggy-3") $
   transLookup2 n1Ref n2Ref $ \x y ->
      transCheck (dedBugcl2 x y)       
-}   
dedBugcl2::Int -> Int -> Proof Statement  -> Bool
dedBugcl2 n1 n2  prf =  fromMaybe False $ do
   st1 <- findNumber n1 prf >>= term
   st2 <- findNumber n2 prf >>= term
   let cs1 = consequent st1
       cs2 = consequent st2
   return (noFit cs1 cs2) 
  where
   noFit  r (p :->: q) = r /= q 
   noFit  _ _          = False  

bugDedcl2 :: Rule (Proof Statement)
bugDedcl2 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggy-3") $
   checkInOut (readRef2 n1Ref n2Ref) (writeRef2 phiRef psiRef) dedBugcl22   
   
dedBugcl22::Trans ((Int, Int), Proof Statement) (SLogic, SLogic)
dedBugcl22 = makeTrans $ \((n1, n2), prf) -> do
   st1 <- findNumber n1 prf >>= term
   st2 <- findNumber n2 prf >>= term
   let cs1 = consequent st1
       cs2 = consequent st2
   guard (noFit cs1 cs2) 
   return (xs cs1 cs2)
  where
   noFit  r (p :->: q) = r /= q 
   noFit  _ _          = False  
   xs  r (p :->: q) = (r, q)
{- 
bugDedcl3 :: Rule (Proof Statement)
bugDedcl3 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggy-4") $
   transLookup2 n1Ref n2Ref $ \x y ->
      transCheck (dedBugcl3 x y)
-}      
bugDedcl3 :: Rule (Proof Statement)
bugDedcl3 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggy-4") $
   checkInOut (readRef2 n1Ref n2Ref) (writeRef2 asRef phiRef) dedBugcl32         
   
dedBugcl3::Int -> Int -> Proof Statement  -> Bool
dedBugcl3 n1 n2  prf =  fromMaybe False $ do
   st1 <- findNumber n1 prf >>= term
   st2 <- findNumber n2 prf >>= term
   let as1 = assumptions st1
       as2 = assumptions st2
       cs2 = consequent st2
   return (noFit as1 as2 cs2) 
  where
   noFit  as1 as2 (p:->: q) = not (as1 `S.isSubsetOf` (S.delete p as2)) 
   noFit  _ _ _         = False    
  
dedBugcl32::Trans ((Int, Int), Proof Statement) ([SLogic], SLogic)
dedBugcl32 = makeTrans $ \((n1, n2), prf) -> do
   st1 <- findNumber n1 prf >>= term
   st2 <- findNumber n2 prf >>= term
   let as1 = assumptions st1
       as2 = assumptions st2
       cs2 = consequent st2
   guard  (noFit as1 as2 cs2)   
   return (xs as1 cs2) 
  where
   noFit  as1 as2 (p:->: q) = not ((S.delete p as1) `S.isSubsetOf` as2) 
   noFit  _ _ _         = False   
   xs as1 (p:->: q) = (S.toList as1, p)
   
bugDedcl4 :: Rule (Proof Statement)
bugDedcl4 = describe "buggy ded" $ buggy $ siblingOf dedId $ ruleTrans (dedId # "buggy-5") $ 
   checkInput2 n1Ref n2Ref dedBugcl4
   
dedBugcl4::Int -> Int -> Proof Statement  -> Bool
dedBugcl4 n1 n2  prf =  fromMaybe False $ do
   st1 <- findNumber n1 prf >>= term
   st2 <- findNumber n2 prf >>= term
   let as1 = assumptions st1
       as2 = assumptions st2
       cs1 = consequent st1
       cs2 = consequent st2
   return (mp as1 as2 cs1 cs2) 
  where
   mp  as1 as2 (p:->: q) r =  ((p `S.insert` as1) `S.isSubsetOf` as2)&& q == r  
   mp  _ _ _ _        = False   
   

   
   
   
testRule::  Int -> Int -> Proof Statement  -> Maybe (Proof Statement)   
testRule  n1 n2  prf |mpMid4 n1 n2  prf   = Just prf
                       |otherwise   = Just mempty
   
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
 
 --      createGoal ([ p, p:->:q, r ]|- q :->: (p :->:r))
 --    >=> return . assumption p
    return . assumption p
     >=> return.assumption (q :->: (p :->:r))
--    >=> return.assumption p 
--   >=> return.assumption ((Not (Not p)) :->: q )
--     >=> modusPonensForward 1 2
--    >=> mpCloseBug1 2 1 1000
     >=> testRule  1000 2 
       
   p = Var (ShowString "p")
   q = Var (ShowString "q")
   r = Var (ShowString "r")
