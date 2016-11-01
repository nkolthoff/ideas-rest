{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Ideas.Rest.Resource.Rule where

import Ideas.Common.Library
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
   toHtml (RRule r) = toHtml (showId r)
   toHtmlRaw = toHtml
   
instance ToHtml [ResourceRule] where
   toHtml xs = ul_ (mconcat (map (li_ . toHtml) xs))
   toHtmlRaw = toHtml
   
instance ToSample ResourceRule where
    toSamples _ = []
