module Main (main) where

import System.Environment (getArgs)
import Control.Exception (throw)

import SessionPi.Language (Proc, preprocess)
import SessionPi.Language.Types (typeCheck)
import SessionPi.Runtime (run)
import SessionPi.Parser (parseProcess)

main :: IO ()
main = getParsedProgram >>= run

getParsedProgram :: IO Proc
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
        Right program -> do
            let check = typeCheck (preprocess program)
            case check of
                Right () -> do
                    print "Typecheck successful!"
                    return program
                Left error -> do
                    print "Typecheck error"
                    print error
                    throw $ userError error
        Left err -> do
            print err
            throw $ userError "Syntax Error"
