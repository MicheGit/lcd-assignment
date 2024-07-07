module Main (main) where

import System.Environment (getArgs)
import Control.Exception (throw)
import Data.List (intercalate)

import SessionPi.Syntax (Proc)
import SessionPi.Types (typeCheck, ndtypeCheck)
import SessionPi.Runtime (run)
import SessionPi.Parser (parseProcess)
import SessionPi.Preprocessing (preprocess)

main :: IO ()
main = getParsedProgram >>= run

getParsedProgram :: IO Proc
getParsedProgram = do
    args <- getArgs
    (nd, filename) <- case args of
            [filename] -> return (False, filename)
            ["nd", filename] -> return (True, filename)
            _ -> do
                print "Missing filename from command line arguments."
                print "Usage: stack run -- path/to/file.spi"
                throw $ userError "Expected Argument Error"
    filecontent <- readFile filename
    let result = parseProcess filename filecontent
        checkFn = if nd then ndtypeCheck else typeCheck
    case result of
        Right raw -> do
            let processed = preprocess raw
            case processed of
                Left err -> do
                    print "Could not infer type for input program"
                    throw $ userError (intercalate "\n\t-" err)
                Right program ->
                    case checkFn program of
                        Right () -> do
                            print "Typecheck successful!"
                            return program
                        Left err -> throw $ userError err
        Left err -> do
            print err
            throw $ userError "Syntax Error"


