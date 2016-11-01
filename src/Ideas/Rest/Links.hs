{-# LANGUAGE RankNTypes #-}

module Ideas.Rest.Links where

import Data.Text
import Ideas.Common.Library
import Ideas.Service.State

data Links = Links 
   { linkExercise :: forall a . Exercise a -> Text
   , linkExamples :: forall a . Exercise a -> Text 
   , linkStrategy :: forall a . Exercise a -> Text 
   , linkRules    :: forall a . Exercise a -> Text 
   , linkState    :: forall a . State a    -> Text
   }