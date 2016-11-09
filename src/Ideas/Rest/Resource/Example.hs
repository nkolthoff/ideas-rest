{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

module Ideas.Rest.Resource.Example where

import Control.Monad
import Ideas.Common.Library
import Data.Aeson.Types
import Data.Function
import Data.List
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

type GetExamplesDifficulty = "examples" :> Capture "difficulty" Difficulty :> Get '[JSON, HTML] ResourceExamples

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
      h2_ $ "Examples (" <> toHtml (show (length xs)) <> ")"
      let grxs = groupBy ((==) `on` fst) $ sortBy (compare `on` fst) xs
      forM_ grxs $ \ys -> do
         h4_ $ toHtml $ show (fst $ head ys) ++ " (" ++ show (length ys) ++ ")"
         p_ $ ul_ [class_ "w3-ul w3-border"] $ mconcat [ li_ $ exampleHtml links ex dif a | (dif, a) <- ys ]
      p_ $ a_ [href_ $ linkAddExample links ex] "Add example"
      
   toHtmlRaw = toHtml
   
exampleHtml :: Monad m => Links -> Exercise a -> Difficulty -> a -> HtmlT m ()
exampleHtml links ex dif a = do
   toHtml (prettyPrinter ex a)
   a_ [class_ "w3-margin-left", href_ (linkState links $ emptyState ex a)] "start"

instance ToSample ResourceExamples where
    toSamples _ = []
   
instance ToSample ResourceExample where
    toSamples _ = []
    
type AddExample = "add-example" :> Get '[JSON, HTML] AddExampleForm

data AddExampleForm = forall a . AddExampleForm Links (Exercise a)

instance ToJSON AddExampleForm where
   toJSON _ = Null

instance ToHtml AddExampleForm where
   toHtml (AddExampleForm links ex) = makePage links (Just ex) $ do
      h1_ "Add example"
      form_ [class_ "w3-container", id_ "add-example"] $ do   
         p_ $ do
            label_ [class_ "w3-label"] "Example"
            input_ [class_ "w3-input w3-border", type_ "text", id_ "example"]
         p_ $ do
            label_ [class_ "w3-label"] "Difficulty"
            br_ []
            input_ [class_ "w3-radio", type_ "radio", name_ "difficulty", value_ "easy"]
            label_ [class_ "w3-validate w3-margin-right"] " easy "
            input_ [class_ "w3-radio", type_ "radio", name_ "difficulty", value_ "medium", checked_]
            label_ [class_ "w3-validate w3-margin-right"] " medium "
            input_ [class_ "w3-radio", type_ "radio", name_ "difficulty", value_ "difficult"]
            label_ [class_ "w3-validate"] " difficult "
         p_ $ button_ [class_ "w3-margin-top w3-btn w3-round-xlarge", onclick_ "addExample()"] "Add"
   
   toHtmlRaw = toHtml

instance ToSample AddExampleForm where
   toSamples _ = []