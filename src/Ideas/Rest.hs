{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}

module Ideas.Rest (restfulMain) where

import Control.Monad
import Data.Aeson.Types
import Data.Text (unpack, pack, Text)
import qualified Data.Text.IO as T (writeFile)
import Servant
import Network.Wai.Handler.Warp (run)
import Ideas.Common.Library
import Ideas.Common.Utils (Some(..))
import Ideas.Service.DomainReasoner
import Ideas.Service.BasicServices
import Ideas.Service.State
import Servant.HTML.Lucid
import Servant.Docs
import Servant.JS
import Lucid
import Ideas.Rest.Links
import Ideas.Rest.Resource.Exercise

links :: Links
links = Links examplesUri strategyUri rulesUri

-----------------------------------------------------------
-- Resources

data ResourceExample = forall a . RExample (Exercise a) Difficulty a

data ResourceStrategy = forall a . RStrategy (LabeledStrategy a)

data ResourceRule = forall a . RRule (Rule a)

data ResourceState = forall a . RState (State a)

instance ToJSON DomainReasoner where
   toJSON dr = String (pack (show (getId dr)))

instance ToJSON ResourceExample where
   toJSON (RExample ex dif a) = String (pack (prettyPrinter ex a ++ " " ++ show dif))

instance ToJSON ResourceStrategy where
   toJSON (RStrategy s) = String (pack (show s))
   
instance ToJSON ResourceRule where
   toJSON (RRule r) = String (pack (show (getId r)))

instance ToJSON ResourceState where
   toJSON (RState st) = String (pack "resource state")

instance ToHtml DomainReasoner where
   toHtml dr = do 
      h1_ $ toHtml $ "Domain Reasoner " ++ showId dr
      ul_ $ forM_ (exercises dr) $ \(Some ex) -> 
        li_ $ a_ [href_ (exerciseUri ex)] (toHtml $ show $ getId ex)
   toHtmlRaw = toHtml

instance ToHtml ResourceRule where
   toHtml (RRule r) = toHtml (showId r)
   toHtmlRaw = toHtml

instance ToHtml ResourceExample where
   toHtml (RExample ex dif a) = 
      toHtml (prettyPrinter ex a ++ " " ++ show dif ++ " ") <>
      p_ (a_ [href_ (stateUri $ emptyState ex a)] (toHtml "start"))
   toHtmlRaw = toHtml 

instance ToHtml ResourceState where
   toHtml (RState st) = 
      toHtml (show st) <>
      case allfirsts st of
         Left msg -> mempty
         Right xs -> ul_ (mconcat 
            [ li_ (a_ [href_ (stateUri newst)] (toHtml (showId r)))
            | ((r, _, _), newst) <- xs, let ex = exercise st, let a = stateTerm newst ])
   toHtmlRaw = toHtml

instance ToHtml [ResourceRule] where
   toHtml xs = ul_ (mconcat (map (li_ . toHtml) xs))
   toHtmlRaw = toHtml
   
instance ToHtml [ResourceExample] where
   toHtml xs = ul_ (mconcat (map (li_ . toHtml) xs))
   toHtmlRaw = toHtml
  
-----------------------------------------------------------
-- API

type IdeasAPI = 
        Get '[JSON, HTML] DomainReasoner
   :<|> "exercises" :> GetExercises
   :<|> ExerciseAPI
   
type ExerciseAPI = Capture "exerciseid" Id :>
   (    GetExercise
   :<|> "examples" :> Get '[JSON, HTML] [ResourceExample]
   :<|> "strategy" :> Get '[JSON] ResourceStrategy
   :<|> "rules" :> Get '[JSON, HTML] [ResourceRule]
   :<|> "state" :> QueryParam "term" String :> QueryParam "prefix" String :> Get '[JSON, HTML] ResourceState
   )

-----------------------------------------------------------
-- Server

ideasServer :: DomainReasoner -> Server IdeasAPI
ideasServer dr =   
        return dr
   :<|> return [ RExercise links ex | Some ex <- exercises dr ]
   :<|> exerciseServer dr
   
exerciseServer :: DomainReasoner -> Server ExerciseAPI
exerciseServer dr s = 
   case findExercise dr s of
      Nothing -> error ("exercise not found: " ++ showId s)
      Just (Some ex) -> 
              return (RExercise links ex) 
         :<|> return [ RExample ex dif a | (dif, a) <- examples ex ]
         :<|> return (RStrategy (strategy ex)) 
         :<|> return [ RRule r | r <- ruleset ex ]
         :<|> \mt mp -> 
                 case maybe (Left "no term") (parser ex) mt of 
                    Left msg -> error msg
                    Right a  -> 
                       case maybe Nothing readPaths mp of
                          Just ps -> return (RState (makeState ex (replayPaths ps (strategy ex) (inContext ex a)) (inContext ex a)))
                          Nothing -> return (RState (emptyState ex a))

-----------------------------------------------------------
-- Main

ideasAPI :: Proxy IdeasAPI
ideasAPI = Proxy

type ExerciseProxy a = Proxy (Capture "exerciseid" Id :> a)

exerciseAPI :: ExerciseProxy GetExercise
exerciseAPI = Proxy

examplesAPI :: ExerciseProxy ("examples" :> Get '[HTML] [ResourceExample])
examplesAPI = Proxy

strategyAPI :: ExerciseProxy ("strategy" :> Get '[JSON] ResourceStrategy)
strategyAPI = Proxy

rulesAPI :: ExerciseProxy ("rules" :> Get '[HTML] [ResourceRule])
rulesAPI = Proxy

stateAPI :: ExerciseProxy ("state" :> QueryParam "term" String :> QueryParam "prefix" String :> Get '[HTML] ResourceState)
stateAPI = Proxy

ideasLink :: (IsElem a IdeasAPI, HasLink a) => Proxy a -> MkLink a
ideasLink = safeLink ideasAPI

showUri :: URI -> Text
showUri x = pack ("/" ++ show x)

exerciseUri, examplesUri, strategyUri, rulesUri :: Exercise a -> Text
exerciseUri ex = showUri $ ideasLink exerciseAPI (getId ex)
examplesUri ex = showUri $ ideasLink examplesAPI (getId ex)
strategyUri ex = showUri $ ideasLink strategyAPI (getId ex)
rulesUri    ex = showUri $ ideasLink rulesAPI    (getId ex)

stateUri :: State a -> Text
stateUri st = pack $ "/" ++ show (safeLink ideasAPI stateAPI (getId st) (Just (prettyPrinter (exercise st) (stateTerm st))) (Just (show (statePrefix st))))

restfulMain :: DomainReasoner -> IO ()
restfulMain dr = run 8081 (serve ideasAPI (ideasServer dr))

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

instance ToSample DomainReasoner where
    toSamples _ = []
    
instance ToSample ResourceState where
    toSamples _ = []
    
instance ToSample ResourceRule where
    toSamples _ = []
    
instance ToSample ResourceStrategy where
    toSamples _ = []
    
instance ToSample ResourceExample where
    toSamples _ = []
    
instance ToParam (QueryParam "prefix" String) where
    toParam _ =
       DocQueryParam "prefix" [] "strategy prefix" Normal
    
instance ToParam (QueryParam "term" String) where
    toParam _ =
       DocQueryParam "term" [] "current term" Normal
    
instance ToCapture (Capture "exerciseid" Id) where
    toCapture _ = 
       DocCapture "exerciseid" "exercise identitifer" 
       
writeMe = writeFile "doc.md" $ markdown $ docs ideasAPI

go = T.writeFile "out.js" $ jsForAPI ideasAPI jquery