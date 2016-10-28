{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}

module Restful (restfulMain) where

import Control.Monad
import Data.Aeson.Types
import Data.Text (unpack, pack)
import Servant
import Network.Wai.Handler.Warp (run)
import Ideas.Common.Library
import Ideas.Common.Utils (Some(..))
import Ideas.Service.DomainReasoner
import Ideas.Service.BasicServices
import Ideas.Service.State
import Servant.HTML.Lucid
import Lucid

-----------------------------------------------------------
-- Resources

data ResourceExercise = forall a . RExercise (Exercise a)

data ResourceExample = forall a . RExample (Exercise a) Difficulty a

data ResourceStrategy = forall a . RStrategy (LabeledStrategy a)

data ResourceRule = forall a . RRule (Rule a)

data ResourceState = forall a . RState (State a)

instance ToJSON DomainReasoner where
   toJSON dr = String (pack (show (getId dr)))

instance ToJSON ResourceExercise where
   toJSON (RExercise ex) = String (pack (show (getId ex)))

instance ToJSON ResourceExample where
   toJSON (RExample ex dif a) = String (pack (prettyPrinter ex a ++ " " ++ show dif))

instance ToJSON ResourceStrategy where
   toJSON (RStrategy s) = String (pack (show s))
   
instance ToJSON ResourceRule where
   toJSON (RRule r) = String (pack (show (getId r)))

instance ToHtml DomainReasoner where
   toHtml dr = do 
      h1_ $ toHtml $ "Domain Reasoner " ++ showId dr
      ul_ $ forM_ (exercises dr) $ \(Some ex) -> 
        li_ $ a_ [href_ (pack $ show $ exerciseUri ex)] (toHtml $ show $ getId ex)
   toHtmlRaw = toHtml

instance ToHtml ResourceExercise where
   toHtml (RExercise ex) = do
      h1_ $ toHtml $ "Exercise " ++ showId ex
      p_ $ a_ [href_ (pack $ show $ examplesUri ex)] (toHtml "examples")
      p_ $ a_ [href_ (pack $ show $ strategyUri ex)] (toHtml "strategy")
      p_ $ a_ [href_ (pack $ show $ rulesUri ex)]    (toHtml "rules")
   toHtmlRaw = toHtml

instance ToHtml ResourceRule where
   toHtml (RRule r) = toHtml (showId r)
   toHtmlRaw = toHtml 

instance ToHtml ResourceExample where
   toHtml (RExample ex dif a) = 
      toHtml (prettyPrinter ex a ++ " " ++ show dif ++ " ") <>
      p_ (a_ [href_ (pack $ show $ stateUri $ emptyState ex a)] (toHtml "start"))
   toHtmlRaw = toHtml 

instance ToHtml ResourceState where
   toHtml (RState st) = 
      toHtml (show st) <>
      case allfirsts st of
         Left msg -> mempty
         Right xs -> ul_ (mconcat 
            [ li_ (a_ [href_ (pack $ show (stateUri newst))] (toHtml (showId r)))
            | ((r, _, _), newst) <- xs, let ex = exercise st, let a = stateTerm newst ])
   toHtmlRaw = toHtml

instance ToHtml [ResourceRule] where
   toHtml xs = ul_ (mconcat (map (li_ . toHtml) xs))
   toHtmlRaw = toHtml
   
instance ToHtml [ResourceExample] where
   toHtml xs = ul_ (mconcat (map (li_ . toHtml) xs))
   toHtmlRaw = toHtml

instance ToHtml [ResourceExercise] where
   toHtml xs = ul_ (mconcat (map (li_ . toHtml) xs))
   toHtmlRaw = toHtml
  
-----------------------------------------------------------
-- API

type IdeasAPI = 
        Get '[JSON, HTML] DomainReasoner
   :<|> "exercises" :> Get '[JSON, HTML] [ResourceExercise]
   :<|> ExerciseAPI
   
type ExerciseAPI = Capture "exerciseid" Id :>
   (    Get '[JSON, HTML] ResourceExercise
   :<|> "examples" :> Get '[JSON, HTML] [ResourceExample]
   :<|> "strategy" :> Get '[JSON] ResourceStrategy
   :<|> "rules" :> Get '[JSON, HTML] [ResourceRule]
   :<|> "state" :> QueryParam "term" String :> QueryParam "prefix" String :> Get '[HTML] ResourceState
   )
   
type SmallAPI = (    Get '[JSON, HTML] ResourceExercise
   :<|> "examples" :> Get '[JSON, HTML] [ResourceExample]
   :<|> "strategy" :> Get '[JSON] ResourceStrategy
   :<|> "rules" :> Get '[JSON, HTML] [ResourceRule]
   :<|> "state" :> QueryParam "term" String :> QueryParam "prefix" String :> Get '[HTML] ResourceState
   )

-----------------------------------------------------------
-- Server

ideasServer :: DomainReasoner -> Server IdeasAPI
ideasServer dr =   
        return dr
   :<|> return [ RExercise ex | Some ex <- exercises dr ]
   :<|> exerciseServer dr
   
exerciseServer :: DomainReasoner -> Server ExerciseAPI
exerciseServer dr s = 
   case findExercise dr s of
      Nothing -> error ("exercise not found: " ++ showId s)
      Just (Some ex) -> 
              return (RExercise ex) 
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

smallAPI :: Proxy SmallAPI
smallAPI = Proxy

type ExerciseProxy a = Proxy (Capture "exerciseid" Id :> a)

exerciseAPI :: ExerciseProxy (Get '[HTML] ResourceExercise)
exerciseAPI = Proxy

examplesAPI :: ExerciseProxy ("examples" :> Get '[HTML] [ResourceExample])
examplesAPI = Proxy

strategyAPI :: ExerciseProxy ("strategy" :> Get '[JSON] ResourceStrategy)
strategyAPI = Proxy

rulesAPI :: ExerciseProxy ("rules" :> Get '[HTML] [ResourceRule])
rulesAPI = Proxy

stateAPI :: Proxy ("state" :> QueryParam "term" String :> QueryParam "prefix" String :> Get '[HTML] ResourceState)
stateAPI = Proxy

exerciseUri, examplesUri, strategyUri, rulesUri :: Exercise a -> URI
exerciseUri ex = safeLink ideasAPI exerciseAPI (getId ex)
examplesUri ex = safeLink ideasAPI examplesAPI (getId ex)
strategyUri ex = safeLink ideasAPI strategyAPI (getId ex)
rulesUri    ex = safeLink ideasAPI rulesAPI    (getId ex)

stateUri :: State a -> URI
stateUri st = safeLink smallAPI stateAPI (Just (prettyPrinter (exercise st) (stateTerm st))) (Just (show (statePrefix st)))

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