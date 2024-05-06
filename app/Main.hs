module Main (main) where

import Text.Read (readMaybe)
import System.Environment (getArgs)
import Control.Exception (throw)

import SessionPi.Language (Proc)
import SessionPi.Runtime (run)
import SessionPi.Parser (parseProcess)

main :: IO ()
main = do 
    (filename, program) <- getParsedProgram
    run program

getParsedProgram :: IO (String, Proc)
getParsedProgram = do
    args <- getArgs
    filename <- case args of
            [filename] -> return filename
            _ -> do
                print "Missing filename from command line arguments."
                print "Usage: cabal run ai -- path/to/file.spi"
                throw $ userError "Expected Argument Error"
    filecontent <- readFile filename
    let result = parseProcess filename filecontent
    case result of
        Right program -> return (filename, program)
        Left err -> do
            print err
            throw $ userError "Syntax Error"
