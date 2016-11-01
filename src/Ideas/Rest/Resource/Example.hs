{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Ideas.Rest.Resource.Example where

import Ideas.Common.Library
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Ideas.Rest.Links
import Servant.Docs
import Servant
import Servant.HTML.Lucid
import Ideas.Service.State

data ResourceExample = forall a . RExample Links (Exercise a) Difficulty a

type GetExamples = "examples" :> Get '[JSON, HTML] [ResourceExample]

instance ToJSON ResourceExample where
   toJSON (RExample _ ex dif a) = String (pack (prettyPrinter ex a ++ " " ++ show dif))
   
instance ToHtml ResourceExample where
   toHtml (RExample links ex dif a) = 
      toHtml (prettyPrinter ex a ++ " " ++ show dif ++ " ") <>
      p_ (a_ [href_ (linkState links $ emptyState ex a)] (toHtml "start"))
   toHtmlRaw = toHtml 
   
instance ToHtml [ResourceExample] where
   toHtml xs = ul_ (mconcat (map (li_ . toHtml) xs))
   toHtmlRaw = toHtml
   
instance ToSample ResourceExample where
    toSamples _ = []