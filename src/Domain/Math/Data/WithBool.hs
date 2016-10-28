{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-----------------------------------------------------------------------------
-- Copyright 2015, Open Universiteit Nederland. This file is distributed
-- under the terms of the GNU General Public License. For more information,
-- see the file "LICENSE.txt", which is included in the distribution.
-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan.heeren@ou.nl
-- Stability   :  provisional
-- Portability :  portable (depends on ghc)
--
-- Values extended with boolean constants
--
-----------------------------------------------------------------------------
--  $Id: WithBool.hs 7527 2015-04-08 07:58:06Z bastiaan $

module Domain.Math.Data.WithBool
   ( WithBool, fromWithBool, join
   ) where

import Control.Applicative
import Control.Monad
import Data.Char (toLower)
import Data.Foldable
import Data.Traversable
import Domain.Logic.Formula
import Ideas.Common.Classes
import Ideas.Common.Rewriting
import Test.QuickCheck

-------------------------------------------------------------------
-- Abstract data type and instances

newtype WithBool a = WB { fromWithBool :: Either Bool a }
   deriving (Eq, Ord, Functor, Arbitrary)

instance Show a => Show (WithBool a) where
   show = either (map toLower . show) show . fromWithBool

instance BoolValue (WithBool a) where
   fromBool = WB . Left
   isTrue   = either id  (const False) . fromWithBool
   isFalse  = either not (const False) . fromWithBool

instance Container WithBool where
   singleton    = WB . Right
   getSingleton = either (const Nothing) Just . fromWithBool

instance Applicative WithBool where
   pure  = singleton
   (<*>) = ap

instance Monad WithBool where
   return  = singleton
   m >>= f = either fromBool f (fromWithBool m)

instance Foldable WithBool where
   foldMap = foldMapDefault

instance Traversable WithBool where
   traverse _ (WB (Left b))  = pure (WB (Left b))
   traverse f (WB (Right a)) = (WB . Right) <$> f a

instance IsTerm a => IsTerm (WithBool a) where
   toTerm = either f toTerm . fromWithBool
    where
      f True  = symbol trueSymbol
      f False = symbol falseSymbol
   fromTerm term
      | isSymbol trueSymbol  term = return true
      | isSymbol falseSymbol term = return false
      | otherwise                 = liftM singleton (fromTerm term)