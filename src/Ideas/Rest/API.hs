{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Ideas.Rest.API where

import Servant
import Ideas.Common.Library
import Ideas.Service.DomainReasoner
import Ideas.Common.Utils
import Ideas.Service.State
import Ideas.Rest.Links
import Ideas.Rest.Resource.Exercise
import Ideas.Rest.Resource.Example
import Ideas.Rest.Resource.State
import Ideas.Rest.Resource.Strategy
import Ideas.Rest.Resource.Rule
import Ideas.Rest.Resource.DomainReasoner

-----------------------------------------------------------
-- API

type IdeasAPI = 
        GetDomainReasoner
   :<|> GetExercises
   :<|> ExerciseAPI
   
type ExerciseAPI = Capture "exerciseid" Id :>
   (    GetExercise
   :<|> GetExamples
   :<|> GetStrategy
   :<|> GetRules
   :<|> "state" :> QueryParam "term" String :> QueryParam "prefix" String :> GetState
   )

-----------------------------------------------------------
-- Server

ideasServer :: Links -> DomainReasoner -> Server IdeasAPI
ideasServer links dr =   
        return (RDomainReasoner links dr)
   :<|> return [ RExercise links ex | Some ex <- exercises dr ]
   :<|> exerciseServer links dr
   
exerciseServer :: Links -> DomainReasoner -> Server ExerciseAPI
exerciseServer links dr s = 
   case findExercise dr s of
      Nothing -> error ("exercise not found: " ++ showId s)
      Just (Some ex) -> 
              return (RExercise links ex) 
         :<|> return [ RExample links ex dif a | (dif, a) <- examples ex ]
         :<|> return (RStrategy (strategy ex)) 
         :<|> return [ RRule r | r <- ruleset ex ]
         :<|> \mt mp -> 
                 case maybe (Left "no term") (parser ex) mt of 
                    Left msg -> error msg
                    Right a  -> 
                       case maybe Nothing readPaths mp of
                          Just ps -> return (RState links (makeState ex (replayPaths ps (strategy ex) (inContext ex a)) (inContext ex a)))
                          Nothing -> return (RState links (emptyState ex a))