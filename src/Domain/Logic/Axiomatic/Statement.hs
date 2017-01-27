{-# LANGUAGE DeriveDataTypeable #-}
module Domain.Logic.Axiomatic.Statement where

import Control.Monad
import Data.List
import Data.String
import Ideas.Common.Library
import Ideas.Text.JSON
import Ideas.Text.Latex
import Domain.Logic.Formula
import Domain.Logic.Parser
import qualified Data.Set as S
import Data.Typeable

infix 2 :|-, |-
 
data Statement = (:|-) { assumptions :: S.Set SLogic, consequent :: SLogic }
   deriving (Eq, Ord, Typeable)

(|-) :: [SLogic] -> SLogic -> Statement
xs |- p = S.fromList xs :|- p

addAssumption :: SLogic -> Statement -> Statement
addAssumption p (ps :|- q) = S.insert p ps :|- q

instance Show Statement where
   show (ps :|- q) = intercalate ", " (map ppLogicPars (S.toList ps)) ++ 
                     " |- " ++ ppLogicPars q

instance Read Statement where
   readsPrec _ s =
      case parseStatement False s of
         Left _ -> []
         Right (ps, q) -> [(ps |- q, "")]

instance Reference Statement

instance IsTerm Statement where
   toTerm st = binary statementSymbol (toTerm (S.toList (assumptions st))) (toTerm (consequent st))
   fromTerm (TCon s [t1, t2]) | s == statementSymbol =
      liftM2 (|-) (fromTerm t1) (fromTerm t2)
   fromTerm _ = fail "invalid statement"
   
instance InJSON Statement where
   toJSON   = toJSON . show
   fromJSON = fromJSON >=> readM

instance ToLatex Statement where
   toLatex st = commas (map slogicToLatex (S.toList (assumptions st)))
                   <> command "vdash" <> slogicToLatex (consequent st)

slogicToLatex :: SLogic -> Latex
slogicToLatex = fromString . show

statementSymbol :: Symbol
statementSymbol = newSymbol "logic.propositional.axiomatic.statement"

subStatement :: Statement -> Statement -> Bool
subStatement (ps :|- p) (qs :|- q) = ps `S.isSubsetOf` qs && p == q

validStatement :: Statement -> Bool
validStatement st =
   tautology (ands (S.toList (assumptions st)) :->: consequent st)
         