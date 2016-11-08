{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

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

data ResourceExamples = forall a . RExamples Links (Exercise a) (Examples a)

data ResourceExample = forall a . RExample Links (Exercise a) Difficulty a

type GetExamples = "examples" :> Get '[JSON, HTML] ResourceExamples

instance ToJSON ResourceExamples where
   toJSON (RExamples links ex xs) =
      toJSON [ RExample links ex dif a | (dif, a) <- xs ]

instance ToJSON ResourceExample where
   toJSON (RExample _ ex dif a) = String (pack (prettyPrinter ex a ++ " " ++ show dif))
   
instance ToHtml ResourceExample where
   toHtml (RExample links ex dif a) = makePage links (Just ex) (exampleHtml links ex dif a)
   toHtmlRaw = toHtml 
   
instance ToHtml ResourceExamples where
   toHtml (RExamples links ex xs) = makePage links (Just ex) $ do
      ul_ $ mconcat [ li_ $ exampleHtml links ex dif a | (dif, a) <- xs ]
      
      form_ [class_ "w3-container", id_ "add-example"] $ do
         label_ [class_ "w3-label"] "Add example"
         input_ [class_ "w3-input", type_ "text", id_ "example"]
         input_ [class_ "w3-radio", type_ "radio", name_ "difficulty", value_ "easy"]
         label_ [class_ "w3-validate"] " easy "
         input_ [class_ "w3-radio", type_ "radio", name_ "difficulty", value_ "medium", checked_]
         label_ [class_ "w3-validate"] " medium "
         input_ [class_ "w3-radio", type_ "radio", name_ "difficulty", value_ "difficult"]
         label_ [class_ "w3-validate"] " difficult "

         p_ $ button_ [class_ "w3-btn", onclick_ "addExample()"] "Add"

   toHtmlRaw = toHtml
   
exampleHtml :: Monad m => Links -> Exercise a -> Difficulty -> a -> HtmlT m ()
exampleHtml links ex dif a =
   toHtml (prettyPrinter ex a ++ " " ++ show dif ++ " ") <>
   p_ (a_ [href_ (linkState links $ emptyState ex a)] "start")

instance ToSample ResourceExamples where
    toSamples _ = []
   
instance ToSample ResourceExample where
    toSamples _ = []