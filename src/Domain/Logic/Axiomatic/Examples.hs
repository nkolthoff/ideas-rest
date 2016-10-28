module Domain.Logic.Axiomatic.Examples 
   ( exampleList, mmExampleList
   ) where

import Ideas.Common.Utils
import Ideas.Common.Library
import Domain.Logic.Formula
import Domain.Logic.Axiomatic.Statement

exampleList :: [(Difficulty, Statement)]
exampleList = 
   [ medium $ [p :->: q] |- (r :->: p) :->: (Not (Not r) :->: q)
   , medium $ [p :->: q] |- (r :->: p) :->: (r :->: q)
   , medium $ [(p :->: q) :->: (p :->: r)] |-  p :->: (q :->: r)
   , medium $ [p :->: (Not q :->: q)] |- p :->: q
   , medium $ [p :->: Not q, r :->: q] |- r :->: Not p
   , medium $ [Not (Not p) :->: (Not q :->: Not (Not q))] |- p :->: q 
   , medium $ [] |- ((p :->: q) :->: p) :->: p
   , medium $ [p :->: Not p] |-  Not p
   , medium $ [p, p :->: q] |- q 
   , medium $ [Not q, p :->: q ] |-  Not p
   , medium $ [Not q :->: Not p] |- p :->: q
   , medium $ [p :->:  q, r :->: Not q] |- r :->: Not p
   , medium $ [p :->:  q, Not p :->: q] |- q
   , medium $ [Not p :->:  q, Not p :->: Not q] |- p
   , medium $ [p :->: q, p:->: Not q] |- Not p
   , medium $ [Not p]|- p :->: q
   , medium $ [p] |- Not (Not p)
   , medium $ [p, Not p] |- q
   , medium $ []|- ((p :->: q) :->: (q :->: p)):->: (q :->: p)
   , medium $ [(p :->: q) :->:r, q]|- r
   --medium $  , [Not (Not p) :->:  Not q, r :->: q ]|- r :->: Not p
   , medium $ [Not (p :->: q)] |- p
   , medium $ [Not (p :->: q)] |- Not q
    ]
 where
   p = Var (ShowString "p") 
   q = Var (ShowString "q")
   r = Var (ShowString "r")
   
mmExampleList :: [(Difficulty, Statement)]
mmExampleList = 
    [ medium $ [p, p :->: q, q :->: r] |- r
    , medium $ [p,  p :->: q] |-  r :->: q
    , medium $ [p :->: (q :->: r)] |- (p :->: q) :->: (p :->: r)
    , medium $ [  q :->: r]|-(p :->: q) :->: (p :->: r)
    , medium $ [p :->: q, p :->: (q :->: r)]|- p :->: r
    , medium $ [p :->: q, q :->: r]|- p :->: r
    , medium $ [ q, p :->: (q :->: r)]|- p :->: r
    , medium $ [] |- p :->: p
    , medium $ [p :->: r] |- p :->: (q :->: r)
    , medium $ [ p:->: (q :->: (r :->: s))] |- p :->: ((q :->: r) :->: (q :->: s))
    , medium $ [p :->: (q :->: r), q :->: (r :->: s)] |- p :->: (q :->: s)
    , medium $ [p :->: r, q :->: (r :->: s)] |- p :->: (q :->: s)
    , medium $ [p :->: (q :->: r)] |- q :->: (p :->: r)
    , medium $ [p :->: (q :->: r),  r :->: s] |-  p :->: (q :->: s)
    , medium $ [p :->: q, r :->: (q :->: s)]|- r :->: (p :->: s)
    , medium $ [] |-  p :->: ((p :->: q) :->: q)
    , medium $ [p :->: (q :->: r),  p:->: (q :->: (r :->: s))] |-  p :->: (q :->: s)
    , medium $ [p :->: r,  p:->: (q :->: (r :->: s))] |-  p :->: (q :->: s)
    , medium $ [p :->: (p :->: q)]|- p :->: q
    , medium $ [ p:->: (q :->: (p :->: r))] |- p :->: (q :->: r) 
    , medium $ []|- (p :->: (p :->: q)) :->: (p :->: q)
    , medium $ [p :->: (q :->: r)] |- p :->: ((s :->: q) :->: (s :->: r))
    , medium $ [] |- (p :->: q) :->: ((r :->: p) :->: (r :->: q))
    ]
 where
   p = Var (ShowString "p") 
   q = Var (ShowString "q")
   r = Var (ShowString "r")  
   s = Var (ShowString "s")
   
medium :: Statement -> (Difficulty, Statement)
medium st = (Medium, st)