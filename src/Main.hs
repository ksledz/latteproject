module Main where

import System.Environment ( getArgs )

import LexLatte
import ParLatte
import TypeChecker
import qualified Data.Text as T
import qualified Data.Maybe
import System.Process
import System.Exit
import System.IO

import ErrM

slash :: T.Text
slash = T.pack("/")
ico :: T.Text
ico = T.pack(".lat")

basename :: T.Text -> T.Text
basename f = Data.Maybe.fromJust(T.stripSuffix ico (last $ T.splitOn slash f))

outputName :: String -> String
outputName f = T.unpack(Data.Maybe.fromJust(T.stripSuffix ico (T.pack f))) ++ ".ll"

basestring :: String -> String
basestring f = T.unpack(basename(T.pack f))

main :: IO ()
main = do
  args <- getArgs
  text <- readFile $ head $ args
  case pProgram $ myLexer $ text of
	Bad s -> die ("ERROR\n" ++ s)
	Ok tree -> do
            case checkTypes tree of 
                Right () -> hPutStrLn stderr "OK"
                Left s -> die ("ERROR\n" ++ s) 
		--writeFile (outputName $ head $ args) (allToLLVM tree)
		--callProcess "llvm-as" [outputName $ head $ args]
