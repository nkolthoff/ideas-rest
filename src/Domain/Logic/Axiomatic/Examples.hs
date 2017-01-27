module Domain.Logic.Axiomatic.Examples 
   ( exampleList, mmExampleList
   ) where

import Ideas.Utils.Prelude
import Ideas.Common.Library
import Domain.Logic.Formula
import Domain.Logic.Axiomatic.Statement

exampleList :: [(Difficulty, Statement)]
exampleList = 
   [ difficult $ [p :->: q] |- (r :->: p) :->: (Not (Not r) :->: q)
   , medium $ [p :->: q] |- (r :->: p) :->: (r :->: q)
   , medium $ [(p :->: q) :->: (p :->: r)] |-  p :->: (q :->: r)
   , difficult $ [p :->: (Not q :->: q)] |- p :->: q
   , difficult $ [p :->: Not q, r :->: q] |- r :->: Not p
   , difficult $ [Not (Not p) :->: (Not q :->: Not (Not q))] |- p :->: q 
   , difficult $ [] |- ((p :->: q) :->: p) :->: p
   , difficult $ [p :->: Not p] |-  Not p
   , easy $ [p, p :->: q] |- q 
   , difficult $ [Not q, p :->: q ] |-  Not p
   , easy $ [Not q :->: Not p] |- p :->: q
   , difficult $ [p :->:  q, r :->: Not q] |- r :->: Not p
   , difficult $ [p :->:  q, Not p :->: q] |- q
   , difficult $ [Not p :->:  q, Not p :->: Not q] |- p
   , difficult $ [p :->: q, p:->: Not q] |- Not p
   , medium $ [Not p]|- p :->: q
   , difficult $ [p] |- Not (Not p)
   , medium $ [p, Not p] |- q
   , difficult $ []|- ((p :->: q) :->: (q :->: p)):->: (q :->: p)
   , medium $ [(p :->: q) :->:r, q]|- r
   --medium $  , [Not (Not p) :->:  Not q, r :->: q ]|- r :->: Not p
   , difficult $ [Not (p :->: q)] |- p
   , difficult $ [Not (p :->: q)] |- Not q
   , difficult $ [q, Not p :->: p] |- p
 --  , medium $ [p, Not q :->: (p :->: Not r)] |-  r :->: q
 --  , medium $ [p :->: r, p :->: (Not q :->: Not r)] |- p :->: q
   , medium $ [(p :->: q) :->: Not p] |- q :->: Not p
   , difficult $ []|- Not (Not (Not q)) :->: Not q
   , easy $ [p, q] |- r :->: q
    ]
 where
   p = Var (ShowString "p") 
   q = Var (ShowString "q")
   r = Var (ShowString "r")
   
mmExampleList :: [(Difficulty, Statement)]
mmExampleList = 
    [ medium $ [p, p :->: q, q :->: r] |- r
    , medium $ [p,  p :->: q] |-  r :->: q
    , medium $ [p :->: (q :->: r) ] |- (p :->: q) :->: (p :->: r)
    , medium $ [p :->: (q :->: r), (p :->: (q :->: r)) :->: ((p :->: q) :->: (p :->: r)) ] |- (p :->: q) :->: (p :->: r)
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
    , medium $ [p :->: (Not q :->: Not r)] |- p :->: (r :->: q)
    , medium $ [p :->: Not q] |- p :->: (q :->: r)
    , medium $ [] |- (Not p :->: (p :->: q))     
    , medium $ [] |- (p :->: (Not p :->: q))
    , medium $ [] |- ((Not p :->:  p) :->: p)
    , medium $ [p :->: (Not q :->: q)] |-  p :->: q
    ]
 where
   p = Var (ShowString "p") 
   q = Var (ShowString "q")
   r = Var (ShowString "r")  
   s = Var (ShowString "s")
   
easy :: Statement -> (Difficulty, Statement)
easy st = (Easy, st)
   
medium :: Statement -> (Difficulty, Statement)
medium st = (Medium, st)

difficult :: Statement -> (Difficulty, Statement)
difficult st = (Difficult, st)


