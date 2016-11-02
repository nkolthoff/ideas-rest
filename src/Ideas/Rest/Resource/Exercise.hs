{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Ideas.Rest.Resource.Exercise where

import Ideas.Common.Library
import Ideas.Rest.HTML.Page
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Ideas.Rest.Links
import Servant.Docs
import Servant
import Servant.HTML.Lucid

data ResourceExercise = forall a . RExercise Links (Exercise a)

type GetExercise  = Get '[JSON, HTML] ResourceExercise
type GetExercises = "exercises" :> Get '[JSON, HTML] [ResourceExercise]

instance ToJSON ResourceExercise where
   toJSON (RExercise _ ex) = String (pack (show (getId ex)))
   
instance ToHtml ResourceExercise where
   toHtml x = makePage $ exerciseHtml x
   toHtmlRaw = toHtml
   
instance ToHtml [ResourceExercise] where
   toHtml xs = makePage $ ul_ (mconcat (map (li_ . exerciseHtml) xs))
   toHtmlRaw = toHtml
   
exerciseHtml :: Monad m => ResourceExercise -> HtmlT m ()
exerciseHtml (RExercise links ex) = do
   h1_ $ toHtml $ "Exercise " ++ showId ex
   p_ $ a_ [href_ (linkExamples links ex)] (toHtml "examples")
   p_ $ a_ [href_ (linkStrategy links ex)] (toHtml "strategy")
   p_ $ a_ [href_ (linkRules links ex)]    (toHtml "rules")
   
instance ToSample ResourceExercise where
    toSamples _ = []