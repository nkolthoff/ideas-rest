{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Ideas.Rest.Resource.Derivation where

import Control.Monad
import Ideas.Common.Library
import Data.Aeson.Types
import Lucid
import Data.Text (pack)
import Ideas.Rest.Links
import Ideas.Rest.HTML.Page
import Ideas.Service.State
import Ideas.Service.BasicServices
import Servant.Docs
import Servant hiding (Context)
import Servant.HTML.Lucid

data ResourceDerivation = forall a . RDerivation Links (Exercise a) (Derivation (Rule (Context a), Environment) (Context a))

type GetDerivation = Get '[JSON, HTML] ResourceDerivation

instance ToJSON ResourceDerivation where
   toJSON (RDerivation _ _ _) = String (pack "derivation")

instance ToHtml ResourceDerivation where
   toHtml (RDerivation links ex d) = makePage links (Just ex) $ do
      h1_ "Solution"
      forM_ (triples d) $ \(ca, (r, env), _) -> do
         p_ $ toHtml $ maybe "" (prettyPrinter ex) $ fromContext ca
         p_ [class_ "w3-margin-left"] $ do
            i_ [class_ "fa fa-long-arrow-right"] mempty
            " " 
            a_ [href_ $ linkRule links ex r] $ toHtml $ showId r
         return ()
      p_ $ do
         toHtml $ maybe "" (prettyPrinter ex) $ fromContext (lastTerm d)
         let icon | maybe False (evalPredicate (ready ex)) (fromContext (lastTerm d)) 
                              = "fa fa-check-circle w3-text-green"
                  | otherwise = "fa fa-times-circle w3-text-red"
         span_ [class_ "w3-margin-left"] $ i_ [class_ icon] mempty
      
      
   toHtmlRaw = toHtml

instance ToSample ResourceDerivation where
    toSamples _ = []