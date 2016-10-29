{-# LANGUAGE RankNTypes #-}

module Links where

import Data.Text
import Ideas.Common.Library

data Links = Links 
   { linkExamples :: forall a . Exercise a -> Text 
   , linkStrategy :: forall a . Exercise a -> Text 
   , linkRules    :: forall a . Exercise a -> Text 
   }