{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module Ideas.Rest (restfulMain, ideasDocs, ideasJS) where

import Data.Text (unpack, pack, Text)
import Servant
import Network.Wai.Handler.Warp (run)
import Ideas.Common.Library
import Ideas.Service.DomainReasoner
import Ideas.Service.State
import Servant.Docs
import Servant.JS
import Ideas.Rest.Links
import Ideas.Rest.Resource.Exercise
import Ideas.Rest.Resource.Example
import Ideas.Rest.Resource.State
import Ideas.Rest.Resource.Strategy
import Ideas.Rest.Resource.Rule
import Ideas.Rest.API

ideasAPI :: Proxy IdeasAPI
ideasAPI = Proxy
   
type ExerciseProxy a = Proxy (Capture "exerciseid" Id :> a)

links :: Links
links = Links 
   { linkExercise = makeLink exerciseAPI . getId
   , linkExamples = makeLink examplesAPI . getId
   , linkStrategy = makeLink strategyAPI . getId
   , linkRules    = makeLink rulesAPI . getId
   , linkState    = \st -> showUri $ ideasLink stateAPI (getId st) (Just (prettyPrinter (exercise st) (stateTerm st))) (Just (show (statePrefix st)))
   }
 where
   makeLink f  = showUri . ideasLink f
   ideasLink x = safeLink ideasAPI x
   showUri x   = pack ("/" ++ show x)
   
   exerciseAPI = Proxy :: ExerciseProxy GetExercise
   examplesAPI = Proxy :: ExerciseProxy GetExamples
   strategyAPI = Proxy :: ExerciseProxy GetStrategy
   
   rulesAPI = Proxy :: ExerciseProxy GetRules
   stateAPI = Proxy :: ExerciseProxy ("state" :> QueryParam "term" String :> QueryParam "prefix" String :> GetState)

-----------------------------------------------------------
-- Main

restfulMain :: DomainReasoner -> IO ()
restfulMain dr = run 8081 (serve ideasAPI (ideasServer links dr))

ideasDocs :: String
ideasDocs = markdown $ docs ideasAPI

ideasJS :: Text
ideasJS = jsForAPI ideasAPI jquery

instance ToHttpApiData Id where
   toUrlPiece = pack . showId

instance FromHttpApiData Id where
   parseUrlPiece = Right . newId . unpack


{-
 
 import Data.String (fromString)
 
data IH

instance Accept IH where
   contentType _ = fromString "text" // fromString "html"
   
instance MimeRender IH DomainReasoner where
  mimeRender _ dr = fromString $ MyHTML.showHTML $ MyHTML.htmlPage "Hello" $ MyHTML.h1 "world"
  
-}
    
instance ToParam (QueryParam "prefix" String) where
    toParam _ =
       DocQueryParam "prefix" [] "strategy prefix" Normal
    
instance ToParam (QueryParam "term" String) where
    toParam _ =
       DocQueryParam "term" [] "current term" Normal
    
instance ToCapture (Capture "exerciseid" Id) where
    toCapture _ = 
       DocCapture "exerciseid" "exercise identitifer" 