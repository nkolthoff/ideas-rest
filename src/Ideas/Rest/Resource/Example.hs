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
import Ideas.Rest.HTML.Page
import Servant.Docs
import Servant
import Servant.HTML.Lucid
import Ideas.Service.State

data ResourceExample = forall a . RExample Links (Exercise a) Difficulty a

type GetExamples = "examples" :> Get '[JSON, HTML] [ResourceExample]

instance ToJSON ResourceExample where
   toJSON (RExample _ ex dif a) = String (pack (prettyPrinter ex a ++ " " ++ show dif))
   
instance ToHtml ResourceExample where
   toHtml x = makePage (exampleHtml x)
   toHtmlRaw = toHtml 
   
instance ToHtml [ResourceExample] where
   toHtml xs = makePage $ ul_ (mconcat (map (li_ . exampleHtml) xs))
   toHtmlRaw = toHtml
   
exampleHtml :: Monad m => ResourceExample -> HtmlT m ()
exampleHtml (RExample links ex dif a) =
   toHtml (prettyPrinter ex a ++ " " ++ show dif ++ " ") <>
   p_ (a_ [href_ (linkState links $ emptyState ex a)] (toHtml "start"))
   
instance ToSample ResourceExample where
    toSamples _ = []