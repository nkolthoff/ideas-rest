{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE OverloadedStrings      #-}

module Ideas.Rest.HTML.Docs (apiToHtml) where

import Control.Lens (mapped, view, (%~), (^.))
import Control.Monad
import Data.ByteString.Lazy.Char8 (ByteString)
import Data.List
import Data.Monoid
import Data.String.Conversions (cs)
import Data.Text (Text, unpack)
import Servant.Docs.Internal
import qualified Data.ByteString.Char8 as BSC
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T
import qualified Network.HTTP.Media as M
import Lucid

apiToHtml :: Monad m => API -> HtmlT m ()
apiToHtml api =
   introsHtml (_apiIntros api) <> mk (map (uncurry endpointHtml) xs)
 where
   xs = sort (HM.toList (_apiEndpoints api))
   
   mk = mconcat . intersperse (hr_ [])

endpointHtml :: Monad m => Endpoint -> Action -> HtmlT m ()
endpointHtml endpoint action = do 
   h2_ $ toHtml $ 
      BSC.unpack (_method endpoint) ++ " " ++ showPath (_path endpoint)
   mkHtml $ notesStr (_notes action)
   authHtml (_authInfo action)
   capturesHtml (_captures action)
   mkHtml $ headersStr (_headers action)
   paramsHtml (_params action)
   rqbodyHtml (_rqtypes action) (_rqbody action)
   responseHtml (_response action)

introsHtml :: Monad m => [DocIntro] -> HtmlT m ()
introsHtml = mconcat . map introHtml

introHtml :: Monad m => DocIntro -> HtmlT m ()
introHtml i = mkHtml $
    ("## " ++ i ^. introTitle) :
    "" :
    intersperse "" (i ^. introBody) ++
    "" :
    []

notesStr :: [DocNote] -> [String]
notesStr = concatMap noteStr

noteStr :: DocNote -> [String]
noteStr nt =
    ("#### " ++ nt ^. noteTitle) :
    "" :
    intersperse "" (nt ^. noteBody) ++
    "" :
    []


authHtml :: Monad m => [DocAuthentication] -> HtmlT m ()
authHtml auths = do
   h4_ "Authentication"
   mkHtml $ mapped %~ view authIntro $ auths
   "Clients must supply the following data"
   mkHtml $ mapped %~ view authDataRequired $ auths

capturesHtml :: Monad m => [DocCapture] -> HtmlT m ()
capturesHtml xs = 
   unless (null xs) $ do
      h4_ "Captures"
      mkList $ map captureHtml xs

captureHtml :: Monad m => DocCapture -> HtmlT m ()
captureHtml cap =
  i_ (toHtml (_capSymbol cap) <> ": ") <> toHtml (_capDesc cap)

headersStr :: [Text] -> [String]
headersStr [] = []
headersStr l = [""] ++ map headerStr l ++ [""]

  where headerStr hname = "- This endpoint is sensitive to the value of the **"
                       ++ unpack hname ++ "** HTTP header."

paramsHtml :: Monad m => [DocQueryParam] -> HtmlT m ()
paramsHtml xs = 
   unless (null xs) $ 
      h4_ "GET Parameters" <>
      mkList (map paramHtml xs)

paramHtml :: Monad m => DocQueryParam -> HtmlT m ()
paramHtml param = do
   toHtml (_paramName param)  
   mkList $ 
      [ b_ "Values: " <> i_ (toHtml (intercalate ", " (_paramValues param)))
      | not (null (_paramValues param)) || _paramKind param /= Flag
      ] ++
      [ b_ "Description: " <> toHtml (_paramDesc param)
      ] ++
      [ "This parameter is a " <> b_ "list" <> ". All GET parameters with the name "
          <> toHtml (_paramName param) <> 
          "[] will forward their values in a list to the handler."
      | _paramKind param == List
      ] ++
      [ "This parameter is a " <> b_ "flag" <> 
        ". This means no value is expected to be associated to this parameter."
      | _paramKind param == Flag
      ]

rqbodyHtml :: Monad m => [M.MediaType] -> [(M.MediaType, ByteString)]-> HtmlT m ()
rqbodyHtml types s =
   unless (null types && null s) $ do
      h4_ "Request"
      mkList (mediaTypesHtml types : map bodyHtml s)

mediaTypesHtml :: Monad m => [M.MediaType] -> HtmlT m ()
mediaTypesHtml ts = 
   unless (null ts) $
      "Supported content types are:"
      <> mkList (map (toHtml . show) ts)

bodyHtml :: Monad m => (M.MediaType, ByteString) -> HtmlT m ()
bodyHtml (m, b) =
  "Example: " <> code_ (toHtml (show m)) <>
  contentHtml m b

markdownForType :: M.MediaType -> String
markdownForType mime_type =
    case (M.mainType mime_type, M.subType mime_type) of
        ("text", "html") -> "html"
        ("application", "xml") -> "xml"
        ("application", "json") -> "javascript"
        ("application", "javascript") -> "javascript"
        ("text", "css") -> "css"
        (_, _) -> ""

-- to do: highlighting as html, xml, javascript, etc.
contentHtml :: Monad m =>  M.MediaType -> ByteString -> HtmlT m ()
contentHtml _mime_type body = pre_ $ toHtml $ (cs body :: String)

contentStr:: M.MediaType -> ByteString -> [String] -- see contentHtml
contentStr mime_type body =
  "" :
  "```" <> markdownForType mime_type :
  cs body :
  "```" :
  "" :
  []

responseHtml :: Monad m => Response -> HtmlT m ()
responseHtml resp = do
   h4_ "Response"
   mkList   
      [ toHtml $ "Status code " ++ show (_respStatus resp)
      , toHtml $ "Headers: " ++ show (_respHeaders resp)
      , mediaTypesHtml (_respTypes resp)
      , case _respBody resp of
           []           -> "No response body"
           [("", t, r)] -> "Response body as below" <> br_ mempty <> mkHtml (contentStr t r)
           xs ->
              mkHtml $ concatMap (\(ctx, t, r) -> ("- " <> T.unpack ctx) : contentStr t r) xs
      ]

mkList :: Monad m => [HtmlT m ()] -> HtmlT m ()
mkList = ul_ . mconcat . map li_

mkHtml :: Monad m => [String] -> HtmlT m ()
mkHtml xs = pre_ $ toHtml $ unlines xs