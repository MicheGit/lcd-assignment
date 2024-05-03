module SessionPi.Parser where

import Data.Void (Void)
import Data.Text (Text)

import Text.Megaparsec (Parsec)

import SessionPi.Language (Proc)

-- Parser :: * -> *
type Parser = Parsec
    Void -- No custom errors
    Text -- Parse Text

-- TODO define tokens, keywords...


parseProc :: Parser Proc
parseProc = undefined
