{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}

module Ideas.Rest.Resource.DomainReasoner where

import Ideas.Common.Library
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Ideas.Rest.Links
import Servant.Docs
import Servant
import Servant.HTML.Lucid
import Ideas.Service.DomainReasoner
import Ideas.Common.Utils
import Control.Monad

data ResourceDomainReasoner = RDomainReasoner Links DomainReasoner

type GetDomainReasoner = Get '[JSON, HTML] ResourceDomainReasoner

instance ToJSON ResourceDomainReasoner where
   toJSON (RDomainReasoner _ dr) = String (pack (show (getId dr)))
   
instance ToHtml ResourceDomainReasoner where
   toHtml (RDomainReasoner links dr) = do 
      h1_ $ toHtml $ "Domain Reasoner " ++ showId dr
      ul_ $ forM_ (exercises dr) $ \(Some ex) -> 
        li_ $ a_ [href_ (linkExercise links ex)] (toHtml $ show $ getId ex)
   toHtmlRaw = toHtml
   
instance ToSample ResourceDomainReasoner where
    toSamples _ = []