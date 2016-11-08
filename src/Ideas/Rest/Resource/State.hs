{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Ideas.Rest.Resource.State where

import Ideas.Common.Library
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Ideas.Rest.Links
import Ideas.Rest.HTML.Page
import Ideas.Service.State
import Ideas.Service.BasicServices
import Servant.Docs
import Servant
import Servant.HTML.Lucid

data ResourceState = forall a . RState Links (State a)

type GetState = Get '[JSON, HTML] ResourceState

instance ToJSON ResourceState where
   toJSON (RState _ _) = String (pack "resource state")
   
instance ToHtml ResourceState where
   toHtml (RState links st) = makePage links (Just (exercise st)) $ do
      toHtml (show st)
      case allfirsts st of
         Left _ -> mempty
         Right xs -> ul_ (mconcat 
            [ li_ (a_ [href_ (linkState links newst)] (toHtml (showId r)))
            | ((r, _, _), newst) <- xs 
            ])
      a_ [href_ $ linkSolution links st] $ "Show solution"
            
   toHtmlRaw = toHtml
   
instance ToSample ResourceState where
    toSamples _ = []
