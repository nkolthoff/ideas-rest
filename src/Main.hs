module Main (main) where

import qualified Data.Text.IO as T
import Ideas.Common.Library
import Ideas.Common.Utils (Some(..))
import qualified Domain.Logic as Logic
import qualified Domain.Logic.Consequence as Logic
import qualified Domain.Logic.Proofs as Logic
import Ideas.Rest
import Ideas.Service.DomainReasoner
import Ideas.Service.ServiceList
import Ideas.Service.Types (Service)

main :: IO ()
main = do
   writeFile "docs/ideas-api.md" ideasDocs
   T.writeFile "docs/ideas-api.js" ideasJS
   restfulMain ideasLogic

-----------------------------------------------------------------

ideasLogic :: DomainReasoner
ideasLogic = describe "Domain reasoner for logic" $
   (newDomainReasoner "ideas.logic")
      { exercises = myExercises
      , services  = myServices
      , aliases   = myAliases
      , scripts   = myScripts
      }

myExercises :: [Some Exercise]
myExercises =
   [ -- logic and relation-algebra
     Some Logic.dnfExercise
   , Some Logic.dnfUnicodeExercise
   , Some Logic.cnfExercise
   , Some Logic.cnfUnicodeExercise
   , Some Logic.proofExercise
   , Some Logic.proofUnicodeExercise
   , Some Logic.proofTopExercise
   , Some Logic.consequenceExercise
   ]

myServices :: [Service]
myServices = metaServiceList ideasLogic ++ serviceList

myAliases :: [(Id, Id)]
myAliases = map (newId *** newId)
   [ ("logic.dnf",                "logic.propositional.dnf")
   , ("logic.dnf-unicode",        "logic.propositional.dnf.unicode")
   , ("logic.proof",              "logic.propositional.proof")
   ]

myScripts :: [(Id, FilePath)]
myScripts =
   [ (getId Logic.dnfExercise,         "logic.txt")
   , (getId Logic.dnfUnicodeExercise,  "logic.txt")
   ]