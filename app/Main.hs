module Main (main) where

import System.Environment (getArgs)
import Control.Exception (throw)

import SessionPi.Syntax (Proc)
import SessionPi.Types (typeCheck)
import SessionPi.Runtime (run)
import SessionPi.Parser (parseProcess)
import SessionPi.Preprocessing (preprocess)

main :: IO ()
main = getParsedProgram >>= run

getParsedProgram :: IO Proc
getParsedProgram = do
    args <- getArgs
    filename <- case args of
            [filename] -> return filename
            _ -> do
                print "Missing filename from command line arguments."
                print "Usage: stack run -- path/to/file.spi"
                throw $ userError "Expected Argument Error"
    filecontent <- readFile filename
    let result = parseProcess filename filecontent
    case result of
        Right raw -> do
            let processed = preprocess raw
            case processed of
                Left err -> do
                    print "Could not infer type for input program"
                    throw $ userError err
                Right program ->
                    case typeCheck program of
                        Right () -> do
                            print "Typecheck successful!"
                            return program
                        Left err -> throw $ userError err
        Left err -> do
            print err
            throw $ userError "Syntax Error"


