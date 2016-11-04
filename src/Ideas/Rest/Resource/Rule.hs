{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Ideas.Rest.Resource.Rule where

import Ideas.Common.Library
import Ideas.Rest.HTML.Page
import Ideas.Rest.Links
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Servant.Docs
import Servant
import Servant.HTML.Lucid

data ResourceRules = forall a . RRules Links [Rule a]

data ResourceRule = forall a . RRule Links (Rule a)

type GetRules = "rules" :> Get '[JSON, HTML] ResourceRules

instance ToJSON ResourceRules where
   toJSON (RRules links rs) = 
      toJSON [ RRule links r | r <- rs ]
   
instance ToJSON ResourceRule where
   toJSON (RRule _ r) = String (pack (show (getId r)))
   
instance ToHtml ResourceRule where
   toHtml (RRule links r) = makePage links Nothing (ruleHtml r)
   toHtmlRaw = toHtml
   
instance ToHtml ResourceRules where
   toHtml (RRules links rs) = makePage links Nothing $ 
      ul_ $ mconcat [ li_ $ ruleHtml r | r <- rs ]
   toHtmlRaw = toHtml
   
ruleHtml :: Monad m => Rule a -> HtmlT m ()
ruleHtml r = toHtml (showId r)

instance ToSample ResourceRules where
    toSamples _ = []

instance ToSample ResourceRule where
    toSamples _ = []
