module Domain.Logic.Axiomatic.Tests (main) where

import Ideas.Common.Library hiding (try, many)
import Domain.Logic.Axiomatic.Exercise (logaxExercise)
import Ideas.Utils.Parsing
import Data.Char
import Data.Maybe

toEnv :: [(String, String)] -> Environment
toEnv = mconcat . map (\(x, y) -> singleBinding (makeRef x) y) 

trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

testStep :: Exercise a -> Rule (Context a) -> Environment -> a -> a -> Either String Environment
testStep ex r env x y =
   case filter (similarity ex (inContext ex y) . fst) outs of
      (_, env):_ -> Right env
      [] -> Left ("\n" ++ unlines (mapMaybe pp outs))
 where
   outs = transApplyWith env (transformation r) (inContext ex x)
   pp (ctx, _) = fmap (prettyPrinter ex) $ fromContext ctx

main :: IO () 
main = do
   txt <- readFile "test.txt"
   case parseSimple parseEntries txt of
      Left msg -> putStrLn msg
      Right es -> do
         putStrLn ("(" ++ show (length es) ++ " entries)")
         sequence_ (zipWith (checkEntry logaxExercise) [1..] es)

checkEntry :: Exercise a -> Int -> Entry -> IO ()
checkEntry ex nr e = do
   putStr (show nr ++ ". ")
   case (parser ex (before e), getRule ex (newId (step e)), parser ex (after e)) of
      (Left msg, _, _) -> do 
         putStrLn "parse error first formula"
         putStrLn msg
      (_, Nothing, _) -> do
         putStrLn ("unknown rule " ++ show (step e)) 
      (_, _, Left msg) -> do
         putStrLn "parse error second formula"
         putStrLn msg
      (Right x, Just r, Right y) -> putStrLn $ 
         case testStep ex r (getEnv e) x y of
            Left msg  -> "rule not recognized: " ++ msg
            Right env 
               | null (bindings env) -> "ok"
               | otherwise -> "ok: {" ++ show env  ++ "}"
            
      

data Entry = Entry 
   { before :: String
   , step   :: String
   , getEnv :: Environment
   , after  :: String
   }

parseEntries :: Parser [Entry]
parseEntries = many parseEntry
   
parseEntry :: Parser Entry
parseEntry = do
   s1  <- manyTill anyChar (try (string "==>"))
   stp <- many (noneOf "{")
   env <- parseEnv
   s2  <- manyTill anyChar (try parseBlankline)
   return $ Entry (trim s1) (trim stp) env (trim s2)

parseEnv :: Parser Environment
parseEnv = do
   char '{'
   bs <- sepBy parseBinding (char ',')
   char '}'
   return $ makeEnvironment bs

parseBinding :: Parser Binding
parseBinding = do 
   key <- many (noneOf ",}=")
   char '='
   val <- many (noneOf ",}=")
   return $ makeBinding (makeRef (trim key)) (trim val)
   
parseBlankline :: Parser ()
parseBlankline = eof <|> do
   char '\n'
   many (oneOf " \t")
   char '\n'
   return ()
