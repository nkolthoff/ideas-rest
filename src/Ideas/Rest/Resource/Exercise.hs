{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

module Ideas.Rest.Resource.Exercise where

import Ideas.Common.Library
import Ideas.Common.Utils
import Ideas.Rest.HTML.Page
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Ideas.Rest.Links
import Servant.Docs
import Servant
import Servant.HTML.Lucid

data ResourceExercises = RExercises Links [Some Exercise]

data ResourceExercise = forall a . RExercise Links (Exercise a)

type GetExercise  = Get '[JSON, HTML] ResourceExercise
type GetExercises = "exercises" :> Get '[JSON, HTML] ResourceExercises

instance ToJSON ResourceExercises where
   toJSON (RExercises links xs) = toJSON [ RExercise links x | Some x <- xs ]
   
instance ToJSON ResourceExercise where
   toJSON (RExercise _ ex) = String (pack (show (getId ex)))
 
instance ToHtml ResourceExercise where
   toHtml (RExercise links ex) = makePage links (Just ex) $ exerciseHtml links ex
   toHtmlRaw = toHtml
   
instance ToHtml ResourceExercises where
   toHtml (RExercises links xs) = makePage links Nothing $ 
      ul_ [class_ "w3-ul w3-hoverable"] $ mconcat $ [ li_ $ a_ [href_ (linkExercise links ex)] $ toHtml (showId ex) | Some ex <- xs ]
   toHtmlRaw = toHtml
   
exerciseHtml :: Monad m => Links -> Exercise a -> HtmlT m ()
exerciseHtml links ex = do
   h1_ $ toHtml $ "Exercise " ++ showId ex
   p_ $ a_ [href_ (linkExamples links ex)] "examples"
   p_ $ a_ [href_ (linkStrategy links ex)] "strategy"
   p_ $ a_ [href_ (linkRules links ex)]    "rules"

instance ToSample ResourceExercises where
    toSamples _ = []
   
instance ToSample ResourceExercise where
    toSamples _ = []