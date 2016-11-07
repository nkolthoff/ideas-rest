{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Ideas.Rest.Resource.API where

import Lucid
import Data.Aeson
import Servant.Docs
import Ideas.Rest.HTML.Docs
import Ideas.Rest.HTML.Page
import Ideas.Rest.Links
import Servant
import Servant.HTML.Lucid

type GetAPI = "api" :> Get '[JSON, HTML] ResourceAPI

data ResourceAPI = ResourceAPI Links API

instance ToJSON ResourceAPI where
   toJSON (ResourceAPI _ s) = toJSON $ markdown s
   
instance ToSample ResourceAPI where
   toSamples _ = []

instance ToHtml ResourceAPI where
   toHtml (ResourceAPI links s) = makePage links Nothing $ apiToHtml s
   toHtmlRaw = toHtml