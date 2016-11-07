{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

module Ideas.Rest.Resource.Rule where

import Ideas.Common.Library
import Ideas.Rest.HTML.Page
import Ideas.Rest.Links
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Servant.Docs
import Servant hiding (Context)
import Servant.HTML.Lucid

data ResourceRules = forall a . RRules Links (Exercise a) [Rule (Context a)]

data ResourceRule = forall a . RRule Links (Exercise a) (Rule (Context a))

type GetRules = "rules" :> Get '[JSON, HTML] ResourceRules

type GetRule = "rules" :> Capture "ruleid" Id :> Get '[JSON, HTML] ResourceRule

instance ToJSON ResourceRules where
   toJSON (RRules links ex rs) = 
      toJSON [ RRule links ex r | r <- rs ]
   
instance ToJSON ResourceRule where
   toJSON (RRule _ _ r) = String (pack (show (getId r)))
   
instance ToHtml ResourceRule where
   toHtml (RRule links ex r) = makePage links (Just ex) (ruleHtml r)
   toHtmlRaw = toHtml
   
instance ToHtml ResourceRules where
   toHtml (RRules links ex rs) = makePage links (Just ex) $ 
      ul_ [class_ "w3-ul w3-hoverable"] $ mconcat [ li_ $ a_ [href_ (linkRule links ex r)] (ruleHtml r) | r <- rs ]
   toHtmlRaw = toHtml
   
ruleHtml :: Monad m => Rule a -> HtmlT m ()
ruleHtml r = toHtml (showId r)

instance ToSample ResourceRules where
    toSamples _ = []

instance ToSample ResourceRule where
    toSamples _ = []
