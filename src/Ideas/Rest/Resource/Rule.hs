{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Ideas.Rest.Resource.Rule where

import Ideas.Common.Library
import Ideas.Rest.HTML.Page
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Servant.Docs
import Servant
import Servant.HTML.Lucid

data ResourceRule = forall a . RRule (Rule a)

type GetRules = "rules" :> Get '[JSON, HTML] [ResourceRule]

instance ToJSON ResourceRule where
   toJSON (RRule r) = String (pack (show (getId r)))
   
instance ToHtml ResourceRule where
   toHtml x = makePage (ruleHtml x)
   toHtmlRaw = toHtml
   
instance ToHtml [ResourceRule] where
   toHtml xs = makePage $ ul_ (mconcat (map (li_ . ruleHtml) xs))
   toHtmlRaw = toHtml
   
ruleHtml :: Monad m => ResourceRule -> HtmlT m ()
ruleHtml (RRule r) = toHtml (showId r)
   
instance ToSample ResourceRule where
    toSamples _ = []
