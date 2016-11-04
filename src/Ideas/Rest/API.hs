{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

{-
$ curl -X POST -d '"~p -> p"' -H 'Accept: application/json' -H 'Content-type: a
pplication/json' http://localhost:8081/logic.propositional.dnf/examples
"~p -> p medium"
-}

module Ideas.Rest.API where

import Control.Monad.IO.Class
import Data.IORef
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
import Servant.Docs

-----------------------------------------------------------
-- API

type IdeasAPI = 
        GetDomainReasoner
   :<|> GetExercises
   :<|> ExerciseAPI
   
type ExerciseAPI = Capture "exerciseid" Id :>
   (    GetExercise
   :<|> GetExamples
   :<|> "examples" :>  ReqBody '[JSON] String :> Post '[JSON] ResourceExample
   :<|> GetStrategy
   :<|> GetRules
   :<|> "state" :> QueryParam "term" String :> QueryParam "prefix" String :> GetState
   )

-----------------------------------------------------------
-- Server

ideasServer :: Links -> IORef DomainReasoner -> Server IdeasAPI
ideasServer links ref =   
   withDomainReasoner ref (RDomainReasoner links)
 :<|> 
   withDomainReasoner ref (RExercises links . exercises)
 :<|> 
   exerciseServer links ref
 
exerciseServer :: Links -> IORef DomainReasoner -> Server ExerciseAPI
exerciseServer links ref s = 
   withExercise ref s (RExercise links) 
 :<|> 
   withExercise ref s (\ex -> RExamples links ex (examples ex))
 :<|> (\txt -> do
   dr <- liftIO (readIORef ref)
   Some ex <- findExercise dr s
   case parser ex txt of 
      Left msg -> fail msg
      Right a  -> do
         liftIO (writeIORef ref dr {exercises = map (\(Some x) -> if getId x == getId ex then Some (ex {examples = (Medium, a) : examples ex}) else Some x) (exercises dr)})
         return (RExample links ex Medium a))
 :<|> 
   withExercise ref s (RStrategy . strategy) 
 :<|> 
   withExercise ref s (RRules links . ruleset)
 :<|> \mt mp -> do
   Some ex <- someExercise ref s
   case maybe (Left "no term") (parser ex) mt of 
      Left msg -> error msg
      Right a  -> 
         case maybe Nothing readPaths mp of
            Just ps -> return (RState links (makeState ex (replayPaths ps (strategy ex) (inContext ex a)) (inContext ex a)))
            Nothing -> return (RState links (emptyState ex a))
       
someExercise :: MonadIO m => IORef DomainReasoner -> Id -> m (Some Exercise)
someExercise ref s = do 
   dr <- liftIO (readIORef ref)
   findExercise dr s

withDomainReasoner :: MonadIO m => IORef DomainReasoner -> (DomainReasoner -> a) -> m a
withDomainReasoner ref f = do 
   dr <- liftIO (readIORef ref)
   return (f dr)
         
withExercise :: MonadIO m => IORef DomainReasoner -> Id -> (forall a . Exercise a -> b) -> m b
withExercise ref s f = do
   Some ex <- someExercise ref s
   return (f ex) 
   
instance ToSample Char