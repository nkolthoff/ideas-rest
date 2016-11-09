{-# LANGUAGE OverloadedStrings #-}
module Ideas.Rest.HTML.Page (makePage) where

import Lucid
import Data.Maybe
import Data.Text
import Ideas.Rest.Links
import Ideas.Common.Library

makePage :: Monad m => Links -> Maybe (Exercise a) -> HtmlT m () -> HtmlT m ()
makePage links mex content = do
   doctype_
   html_ $ do
      title_ "Title"
      meta_ [name_ "viewport", content_ "width=device-width, initial-scale=1"]
      link_ [rel_ "icon", type_ "image/png", href_ "http://ideas.cs.uu.nl/images/star.png"]
      stylesheet "http://www.w3schools.com/lib/w3.css"
      stylesheet "http://www.w3schools.com/lib/w3-theme-blue.css"
      stylesheet "https://fonts.googleapis.com/css?family=Roboto"
      stylesheet "https://cdnjs.cloudflare.com/ajax/libs/font-awesome/4.6.3/css/font-awesome.min.css"
      termWith "script" [src_ "http://code.jquery.com/jquery-3.1.1.min.js"] mempty
      style_ styleTxt
      body_ $ do
         navBar links
         case mex of
            Just ex -> sidenav links ex
            Nothing -> return ()
         overlayEffect
         div_ ([class_ "w3-main"] ++ [ style_ "margin-left:175px" | isJust mex]) $ do
            div_ [class_ "w3-row w3-padding-16 w3-margin-left w3-margin-right"] $ p_ [class_ "w3-padding-16"] mempty <> content
            footer
         script_ (scriptTxt <> "\n" <> maybe mempty extraTxt mex)
   
styleTxt :: Text
styleTxt =
   "html,body,h1,h2,h3,h4,h5,h6 {font-family: \"Roboto\", sans-serif}\n\
   \h1,h2,h3,h4,h5,h6 {color: #085a9d;}\n\
   \.w3-sidenav a,.w3-sidenav h4 {padding: 12px;}\n\
   \.w3-navbar li a {\n\
   \    padding-top: 12px;\n\
   \    padding-bottom: 12px;\n\
   \}"
   
navBar :: Monad m => Links -> HtmlT m ()
navBar links = div_ [class_ "w3-top"] $ do
   ul_ [class_ "w3-navbar w3-theme w3-top w3-left-align w3-large"] $ do
      li_ [class_ "w3-opennav w3-right w3-hide-large"] $
         a_ [class_ "w3-hover-white w3-large w3-theme-l1", href_ "javascript:void(0)", onclick_ "w3_open()"] $
            i_ [class_ "fa fa-bars"] $ mempty
      li_ $ a_ [href_ "http://ideas.cs.uu.nl/", class_ "w3-theme-l1"] "Ideas"
      li_ [class_ "w3-hide-small"] $
         a_ [href_ (linkTop links), class_ "w3-hover-white"] $ do
            i_ [class_ "fa fa-home w3-large"] mempty
            " Domain Reasoner"
      li_ [class_ "w3-hide-small"] $
         a_ [href_ (linkExercises links), class_ "w3-hover-white"] "Exercises"
      li_ [class_ "w3-hide-small"] $
         a_ [href_ (linkAPI links), class_ "w3-hover-white"] "API"

sidenav :: Monad m => Links -> Exercise a -> HtmlT m ()
sidenav links ex = nav_ [class_ "w3-sidenav w3-collapse w3-theme-l5", style_ "z-index:3;width:175px;margin-top:51px;", id_ "mySidenav"] $ do
   a_ [href_ "javascript:void(0)", onclick_ "w3_close()", class_ "w3-right w3-xlarge w3-padding-large w3-hover-black w3-hide-large", title_ "close menu"] $
      i_ [class_ "fa fa-remove"] mempty
   h4_ $ b_ "Exercise"
   a_ [href_ (linkExercise links ex), class_ "w3-hover-black"] "Information"
   a_ [href_ (linkExamples links ex), class_ "w3-hover-black"] "Examples"
   a_ [href_ (linkRules links ex), class_ "w3-hover-black"] "Rules"
   a_ [href_ (linkStrategy links ex), class_ "w3-hover-black"] "Strategy"

footer :: Monad m => HtmlT m ()
footer = footer_ [id_ "myFooter"] $ do
   div_ [class_ "w3-container w3-theme-l1"] $
      p_ $ do
         "Powered by "
         a_ [href_ "http://www.w3schools.com/w3css/default.asp", target_ "_blank"] $
            "w3.css"

overlayEffect :: Monad m => HtmlT m ()
overlayEffect = 
   div_ [class_ "w3-overlay w3-hide-large", onclick_ "w3_close()", style_ "cursor:pointer", title_ "close side menu", id_ "myOverlay"] mempty

scriptTxt :: Text
scriptTxt =
   "// Get the Sidenav\n\
   \var mySidenav = document.getElementById(\"mySidenav\");\n\
   \// Get the DIV with overlay effect\n\
   \var overlayBg = document.getElementById(\"myOverlay\");\n\
   \// Toggle between showing and hiding the sidenav, and add overlay effect\n\
   \function w3_open() {\n\
   \    if (mySidenav.style.display === 'block') {\n\
   \        mySidenav.style.display = 'none';\n\
   \        overlayBg.style.display = \"none\";\n\
   \    } else {\n\
   \        mySidenav.style.display = 'block';\n\
   \        overlayBg.style.display = \"block\";\n\
   \    }\n\
   \}\n\
   \// Close the sidenav with the close button\n\
   \function w3_close() {\n\
   \    mySidenav.style.display = \"none\";\n\
   \    overlayBg.style.display = \"none\";\n\
   \}"
   
extraTxt :: Exercise a -> Text 
extraTxt ex =
   "var exid = '" <> pack (showId ex) <> "';\n\
   \function addExample() {\n\
   \  alert($('input[name=difficulty]:checked', '#add-example').val());\n\
   \  postByExerciseidExamples(exid, {expr: $('#example').val(), difficulty: $('input[name=difficulty]:checked', '#add-example').val()}, null, null);\n\
   \}\n\
   \var postByExerciseidExamples = function(exerciseid, body, onSuccess, onError)\n\
   \{\n\
   \  $.ajax(\n\
   \    { url: '/' + encodeURIComponent(exerciseid) + '/examples'\n\
   \    , success: onSuccess\n\
   \    , data: JSON.stringify(body)\n\
   \    , contentType: 'application/json'\n\
   \    , error: onError\n\
   \    , type: 'POST'\n\
   \    });\n\
   \}"

stylesheet :: Monad m => Text -> HtmlT m ()
stylesheet url = link_ [rel_ "stylesheet", href_ url]