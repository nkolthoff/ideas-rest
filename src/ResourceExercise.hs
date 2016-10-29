{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}

module ResourceExercise where

import Ideas.Common.Library
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Links
import Servant.Docs
import Servant
import Servant.HTML.Lucid

data ResourceExercise = forall a . RExercise Links (Exercise a)

type GetExercise  = Get '[JSON, HTML] ResourceExercise
type GetExercises = Get '[JSON, HTML] [ResourceExercise]

instance ToJSON ResourceExercise where
   toJSON (RExercise _ ex) = String (pack (show (getId ex)))
   
instance ToHtml ResourceExercise where
   toHtml (RExercise links ex) = do
      h1_ $ toHtml $ "Exercise " ++ showId ex
      p_ $ a_ [href_ (linkExamples links ex)] (toHtml "examples")
      p_ $ a_ [href_ (linkStrategy links ex)] (toHtml "strategy")
      p_ $ a_ [href_ (linkRules links ex)]    (toHtml "rules")
   toHtmlRaw = toHtml
   
instance ToHtml [ResourceExercise] where
   toHtml xs = ul_ (mconcat (map (li_ . toHtml) xs))
   toHtmlRaw = toHtml
   
instance ToSample ResourceExercise where
    toSamples _ = []